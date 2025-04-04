from functools import reduce
from itertools import groupby
import sys

from dpn.expr import Expr
from encoding.encoding import *
from uncertainty.trace import UncertainTrace
from utils import pad_to

MAX = 100
DROP_MOVE = 0
LOG_MOVE = 1
MODEL_MOVE = 2
SYNC_MOVE = 3

class UncertaintyEncoding(Encoding):

  def __init__(self, dpn, solver, step_bound, ukind):
    super().__init__(dpn, solver, step_bound)
    self._uncertainty_kind = ukind
  
  def edit_distance_vars(self, trace_len):
    s = self._solver
    def var(i, j):
      name = "d" + str(i) + "_" + str(j)
      if self._uncertainty_kind == "min":
        return s.intvar(name) if i > 0 or j>0 else s.num(0)
      else:
        return s.realvar(name) if i > 0 or j>0 else s.real(0)
    return [[var(i,j) \
      for j in range(0, trace_len+1)] for i in range(0, self._step_bound+1)]

  def move_type_vars(self, trace_len):
    s = self._solver
    var = lambda i, j: s.intvar("movetype" + str(i) + "_" + str(j))
    xs = [[var(i,j) \
      for j in range(0, trace_len+1)] for i in range(0, self._step_bound+1)]
    self._vs_syn_move = [[None for j in range(0, trace_len+1)] \
      for i in range(0, self._step_bound+1)]
    drop_move = s.num(DROP_MOVE)
    log_move = s.num(LOG_MOVE)
    mod_move = s.num(MODEL_MOVE)
    sync_move = s.num(SYNC_MOVE)
    for i in range(0, self._step_bound+1):
      for j in range(0, trace_len+1):
        self._vs_log_move[i][j] = s.eq(xs[i][j], log_move)
        self._vs_mod_move[i][j] = s.eq(xs[i][j], mod_move)
        self._vs_syn_move[i][j] = s.eq(xs[i][j], sync_move)
        if i>0 or j > 0:
          s.require([s.lor([self._vs_log_move[i][j], self._vs_mod_move[i][j], self._vs_syn_move[i][j], s.eq(xs[i][j], drop_move)])])
        if i ==0:
          # no (silent) model, no sync move
          s.require([s.neg(s.eq(xs[i][j], sync_move)), \
            s.neg(s.eq(xs[i][j], mod_move)) ])
        if j > 0:
          s.require([s.iff(s.eq(xs[i][j], drop_move), self._vs_drop[j-1])]) 
        else:
          # no drop, no syn, no log
          s.require([s.neg(s.eq(xs[i][j], drop_move)), \
            s.neg(s.eq(xs[i][j], sync_move)), s.neg(s.eq(xs[i][j], log_move))])
    return xs

  def prepare_edit_distance(self, trace_len):
    super().prepare_edit_distance(trace_len)
    s = self._solver
    self._silents = [s.boolvar("silent"+str(i)) for i in range(0,self._step_bound) ]
    self._vs_drop = [ s.boolvar("drop" + str(j)) for j in range(0, trace_len)]
    self._vs_act = [ s.intvar("act" + str(j)) for j in range(0, trace_len)]
    self._vs_move_type = self.move_type_vars(trace_len)

  def order_constraints(self, trace):
    m = len(trace)
    s = self._solver
    events = trace._events

    vs_time = [ (e, s.realvar("time" + str(j)), s.intvar("pos" + str(j))) \
      for (j, e) in enumerate(events) ] #T_ei and P_ei
    vs_trace = [ s.intvar("tracetime" + str(j)) for j in range(0, m)]  # L_i
    self._vs_trace = vs_trace
    self._vs_time = dict([ (e._id, v) for (e,v,_) in vs_time])
    self._vs_pos = dict([ (e._id, v) for (e,_,v) in vs_time])

    # time values for events are in range
    cs = []
    for (e, v, _) in vs_time:
      low = s.real(e.lower_time())
      if e._time.is_uncertain():
        upp = s.real(e.upper_time())
        cs += [s.ge(upp, v), s.ge(v, low)]
      else:
        cs.append(s.eq(v, low))

    # values taken by vs_trace are ids of events
    for j in range(0,m):
      cs += [s.lor([s.eq(vs_trace[j], s.num(id)) for id in self._vs_time.keys()])]
    
    pairs = [ (e1, e2) for e1 in vs_time for e2 in vs_time if e1 != e2]
    # position and time
    cs.append(s.distinct([ vp for (_, _, vp) in vs_time ]))
    for ((e1, vt1, vp1), (e2, vt2, vp2)) in pairs:
      cs.append(s.implies(s.lt(vp1, vp2), s.le(vt1, vt2)))
      cs.append(s.implies(s.lt(vt1, vt2), s.lt(vp1, vp2)))

    # nth-event variables are inverse of position variables 
    for (e, _, vp) in vs_time:
      for j in range(0,m):
        cs.append(s.iff(s.eq(vp, s.num(j)), s.eq(vs_trace[j], s.num(e._id))))
    
    return (vs_trace, s.land(cs))

  def trace_constraints(self, trace):
    s = self._solver
    vs_act = self._vs_act
    cs = []
    for j in range(0, len(trace)):
      event = trace._events[j]
      labels = event._activity._activities
      cs += [s.le(s.num(0), vs_act[j]), s.lt(vs_act[j], s.num(len(labels)))]
      if not event.is_uncertain():
        cs.append(s.neg(self._vs_drop[j]))
    return s.land(cs)


  # return pair of edit distance expression and side constraints
  def edit_distance_parametric(self, trace, costs):
    (lcost, mcost, syncost, drop_cost) = costs
    # lcost, mcost, syncost, pcost are costs of log, model, synchronous, and
    # projection/skip moves; they all take only the index/indices as arguments
    delta = self._vs_dist
    n = self._step_bound
    m = len(trace)
    s = self._solver
    dpn = self._dpn
    etrans = [(t["id"], t) for t in dpn.transitions()]
    vs_drop = self._vs_drop
    vs_log = self._vs_log_move
    vs_mod = self._vs_mod_move
    vs_syn = self._vs_syn_move

    def is_silent(i): # transition i is silent
      return s.lor([ s.eq(self._vs_trans[i], s.num(id)) \
        for (id, t) in etrans if t in dpn.reachable(i) and t["invisible"] ])
    
    is_silents = [ is_silent(i) for i in range(0,n) ]
    silent_def = [ s.iff(v,e) for (v,e) in zip(self._silents, is_silents)]
    mcostmod = lambda i: s.ite(self._silents[i], s.num(0), mcost(i))
    # caching
    mcostsmod = [ s.realvar("mcost" + str(i)) for i in range(0,n)]
    mcostsmod_def = [ s.eq(mcostsmod[i],mcostmod(i)) for i in range(0,n) ]
    lcosts = [ s.realvar("lcost" + str(j)) for j in range(0,m)]
    lcosts_def = [ s.eq(lcosts[j],lcost(j)) for j in range(0,m) ]

    # delta[i][j] represents the edit distance of transition sequence up to
    # including i, and the log up to including j
    # optimization: constraints of form delta[i+1][j+1] = e are equivalent to
    # delta[i+1][j+1] >= e due to minimization. replaced some for performance.
    # (but not always, sometimes = seems better)

    # 1. all intermediate distances delta[i][j] are non-negative
    non_neg = [s.ge(delta[i][j], s.num(0))\
      for i in range(0,n+1) for j in range(0,m+1)]
    # 2. if the ith transition is not silent, delta[i+1][0] = delta[i][0] + P_M
    model0 = [ s.ge(delta[i+1][0], s.plus(mcostsmod[i], delta[i][0])) \
        for i in range(0,n) ]
    # 3. delta[0][j+1] = delta[0][j] + ite(drop(j), P_drop, P_L)
    log0 = [ s.land([
      s.implies(vs_log[0][j+1], s.eq(delta[0][j+1], s.plus(delta[0][j], lcosts[j]))),
      s.implies(vs_drop[j], s.ge(delta[0][j+1], s.plus(drop_cost(j), delta[0][j]))) \
      ]) for j in range(0,m) ]

    # 4. encode delta[i+1][j+1] >= min(...) as one of
    #  delta[i+1][j+1] >= delta[i][j] + sync move penalty
    #  delta[i+1][j+1] >= delta[i+1][j] + log move or drop penalty
    #  delta[i+1][j+1] >= delta[i+1][j] + model move penalty

    steps = []
    for i in range(0,n):
      reachable_labels = set([ t["label"] for k in range(i-1, n) for t in dpn.reachable(k)])
      for j in range(0,m):
        log_step = s.implies(vs_log[i+1][j+1], \
          s.ge(delta[i+1][j+1],s.plus(lcosts[j], delta[i+1][j])))
        drop_step = s.implies(vs_drop[j], \
          s.eq(delta[i+1][j+1],s.plus(drop_cost(j), delta[i+1][j])))
        
        if len(reachable_labels) > 0 or j == 0 or j == m-1:
          mod_step = s.implies(vs_mod[i+1][j+1], s.eq(delta[i+1][j+1], s.plus(mcostsmod[i],delta[i][j+1])))
        else:
          mod_step = s.neg(vs_mod[i+1][j+1])
        inter = set(trace[j]._activity.labels()).intersection(set(reachable_labels))
        if len(inter) > 0:
          syn_step = s.implies(vs_syn[i+1][j+1], s.ge(delta[i+1][j+1], \
            s.plus(syncost(i, j), delta[i][j])))
        else:
          syn_step = s.neg(vs_syn[i+1][j+1])
        steps += [log_step, drop_step, mod_step, syn_step]

    #steps = [ s.lor([s.eq(delta[i+1][j+1], s.plus(syncost(i, j), delta[i][j])),\
    #                 s.eq(delta[i+1][j+1], s.plus(lcost(j), delta[i+1][j])), \
    #                 s.land([vs_drop[j], s.eq(delta[i+1][j+1], s.plus(drop_cost(j), delta[i+1][j]))]), \
    #                 s.eq(delta[i+1][j+1], s.plus(mcostmod(i),delta[i][j+1]))])\
    #  for i in range(0,n) for j in range(0,m) ]

    #FIXME symmetry breaking: enforce log steps before model steps?
    # perhaps does not always pay off
    symm = []
    for i in range(2,n):
      for j in range(3,m):
        symm.append(s.implies(vs_mod[i][j-1], s.neg(vs_log[i][j])))

    # run length, only relevant for multiple tokens
    length = [s.ge(self._run_length, s.num(0)),s.ge(s.num(n), self._run_length)]
    
    if self._dpn.has_final_places():
      min_expr = delta[n][m]
    else:
      min_expr = delta[0][m]
      for i in range(1,n+1):
        min_expr = s.ite(s.eq(self._run_length, s.num(i)), delta[i][m],min_expr)

    constraints = non_neg + model0 + log0 + steps + length + silent_def + symm \
      + mcostsmod_def + lcosts_def
    return (min_expr, s.land(constraints))


  def edit_distance_min_fixed_order(self, trace):
    s = self._solver
    cost1 = lambda _ : s.num(1)
    dropcost = lambda i: s.num(0 if trace._events[i].is_uncertain() else MAX)
    
    def syncost(i,j):
      # in min, data difference is ignored
      is_poss_label = [s.eq(self._vs_trans[i], s.num(t["id"])) \
        for t in self._dpn.reachable(i) \
        if "label" in t and t["label"] in trace._events[j].labels() ]
      return s.ite(s.lor(is_poss_label), s.num(0), s.num(MAX))
  
    self._penalties = (cost1, cost1, syncost, dropcost)
    return self.edit_distance_parametric(trace, self._penalties)
  

  def edit_distance_min_var_order(self, trace):
    s = self._solver
    one = s.num(1)
    # vs_trace[i] gets value of trace event id that is taken at instant i
    vs_trace, order_constr = self.order_constraints(trace)

    cost1 = lambda _ : one
    indet_events = [ e._id for e in trace._events if e.is_uncertain()]
    def pcost(i):
      is_indet_id = s.lor([s.eq(vs_trace[i], s.num(id)) for id in indet_events]) 
      return s.ite(is_indet_id, s.num(0),s.num(MAX))
    
    def syncost(i,j):
      poss_labels = []
      trans_events = [ (t,e) \
        for t in self._dpn.reachable(i) for e in trace._events \
        if "label" in t and t["label"] in e.labels()]
      for (t,e) in trans_events:
        is_event = s.eq(vs_trace[j], s.num(e._id))
        is_trans = s.eq(self._vs_trans[i], s.num(t["id"]))
        poss_labels.append(s.land([is_event, is_trans]))
      return s.ite(s.lor(poss_labels), s.num(0), s.num(MAX))
  
    self._penalties = (cost1, cost1, syncost, pcost)
    emin,cs = self.edit_distance_parametric(trace, self._penalties)
    return (emin, s.land([cs, order_constr]))
  

  def edit_distance_min(self, trace):
    if not trace.has_uncertain_time():
      return self.edit_distance_min_fixed_order(trace)
    else:
      return self.edit_distance_min_var_order(trace)


  def write_diff_var(self, trace, t, i, j):
    s = self._solver
    subst_prime = dict([ (x, v) for (x, v) in self._vs_data[i+1].items() ])
    vs_trace = self._vs_trace
    diff = s.num(0)
    for x in t["write"]:
      is_ok = []
      for e in trace._events:
        is_event = s.eq(vs_trace[j], s.num(e._id))
        if e.has_data_variable(x): #otherwise written mismatch, so increase diff
          data = e.data_variable(x)
          if data.is_discrete():
            vs = [s.eq(subst_prime[x],s.real(Expr.numval(v))) for v in data.values()]
            is_ok.append(s.land([is_event, s.lor(vs)]))
          else:
            low, upp = data.bounds()
            in_bounds = [ s.le(s.real(Expr.numval(low)), subst_prime[x]), \
              s.le(s.real(subst_prime[x], Expr.numval(upp))) ]
            is_ok.append(s.land([is_event, s.land(in_bounds)]))
      diff = s.ite(s.lor(is_ok), diff, s.inc(diff))
    return diff


  def sync_costs_var(self, trace, i, j):
    vs_trace = self._vs_trace
    s = self._solver

    ps = []
    zero = s.real(0)
    trans_events = [ (t, y, e) \
      for t in self._dpn.reachable(i) for (y,e) in enumerate(trace._events) \
      if "label" in t and t["label"] in e.labels()]
    for (t, y, e) in trans_events:
      is_t = s.eq(self._vs_trans[i], s.num(t["id"]))
      is_event = s.eq(vs_trace[j], s.num(e._id))
      conf = e.indeterminacy()
      activities = e._activity._activities.items()
      wdiff = None
      for (k, (lab, p)) in enumerate(activities):
        if "label" in t and t["label"] == lab:
          # FIXME is the following needed?
          print(self._vs_pos)
          is_act = s.eq(self._vs_act[y], s.num(k))
          theta = s.real(2 - p - conf)
          if wdiff == None:
            wdiff = self.write_diff_var(trace, t, i, j)
          penalty = s.ite(s.eq(wdiff, zero), theta, s.mult(wdiff, theta))
          ps.append((s.land([is_event, is_act, is_t]), penalty))
    return ps


  def edit_distance_fitness_var_order(self, trace):
    s = self._solver
    vs_act = self._vs_act
    vs_trace, order_constr = self.order_constraints(trace)

    def drop_cost(i):
      cost_expr = s.real(MAX)
      for e in trace._events:
        is_event = s.eq(vs_trace[i], s.num(e._id))
        cost_expr = s.ite(is_event, s.real(e.indeterminacy()), cost_expr)
      return cost_expr
    
    def lcost(j):
      cost_expr = s.real(MAX)
      for (k, e) in enumerate(trace._events):
        is_event = s.eq(vs_trace[j], s.num(e._id))
        labels = e._activity._activities.items()
        conf = e.indeterminacy()
        cost_e = s.real(MAX)
        for (k, (l,p)) in enumerate(labels):
          # 1 + (1-p) + (1-conf) = 3 - p - conf
          cost_e = s.ite(s.eq(vs_act[j], s.num(k)), s.real(3 - p - conf), cost_e)
        cost_expr = s.ite(is_event, cost_e, cost_expr)
      return cost_expr
    
    def syncost(i,j):
      e = s.real(MAX)
      for (is_t, penalty) in self.sync_costs_var(trace, i, j):
        e = s.ite(is_t, penalty, e)
      return e
    
    def mcost(i):
      e = s.real(MAX)
      for t in self._dpn.reachable(i):
        e = s.ite(s.eq(self._vs_trans[i], s.num(t["id"])), s.num(len(t["write"]) + 1), e)
      return e

    self._penalties = (lcost, mcost, syncost, drop_cost)
    (min_expr, cs) = self.edit_distance_parametric(trace, self._penalties)
    return (min_expr, s.land([order_constr, cs]))


  def write_diff_fixed(self, trace, i, j, t):
    subst_prime = dict([ (x, v) for (x, v) in self._vs_data[i+1].items() ])
    s = self._solver
    diff = s.num(0)
    vcount = 0
    for x in t["write"]:
      if not trace[j].has_data_variable(x): # x not in trace[j].data():
        diff = s.inc(diff) 
      else:
        xvals = trace[j].data_variable(x)
        if xvals.is_discrete(): 
          vals = xvals.values()
          if len(vals) == 1:
            val = Expr.numval(vals[0])
            matches = s.eq(subst_prime[x], s.real(val))
          else:
            matches = s.lor([s.eq(subst_prime[x], s.real(Expr.numval(v))) \
              for v in vals]) 
        else:
          low, upp = xvals.bounds()
          matches = s.land([ s.le(s.real(Expr.numval(low)), subst_prime[x]), \
            s.le(subst_prime[x], s.real(Expr.numval(upp))) ])
        #mvar = s.boolvar("match"+str(i)+"_"+str(j)+"_"+str(vcount))
        vcount += 1
        #s.require(s.iff(mvar, matches))
        diff = s.ite(matches, diff, s.inc(diff))
    return diff


  def sync_costs_fixed_order(self, trace, i, j):
    s = self._solver
    # possible activities for jth trace element
    activities = trace._events[j]._activity._activities.items()
    # confidence of jth trace element
    conf = trace._events[j].indeterminacy()

    ps = []
    zero = s.real(0)
    for t in self._dpn.reachable(i):
      wdiff = self.write_diff_fixed(trace, i, j, t)
      is_t = s.eq(self._vs_trans[i], s.num(t["id"]))
      for (k, (l, p)) in enumerate(activities):
        if "label" in t and t["label"] == l: # transition t matches kth activity
          is_act = s.eq(self._vs_act[j], s.num(k))
          theta = s.real(2 - p - conf)
          theta1 = s.real(3 - p - conf)
          penalty = s.ite(s.eq(wdiff, zero), theta, s.mult(wdiff, theta1))
          ps.append((s.land([is_act, is_t]), penalty))
    return ps


  def edit_distance_fitness_fixed_order(self, trace):
    assert(isinstance(trace, UncertainTrace))
    s = self._solver

    def drop_cost(i):
      e = s.real(trace._events[i].indeterminacy()) \
        if trace._events[i].is_uncertain() else s.real(MAX)
      return e
    
    def lcost(j):
      event = trace._events[j]
      labels = event._activity._activities.items()
      conf = event.indeterminacy()
      vs_act = self._vs_act
      if len(labels) == 1:
        return s.real(2 - conf)
      else:
        e = s.real(MAX)
        for (k, (l,p)) in enumerate(labels):
          # 1 + (1-p) + (1-conf) = 3 - p - conf
          e = s.ite(s.eq(vs_act[j], s.num(k)), s.real(3 - p - conf), e)
        return e
    
    def mcost(i):
      e = s.real(MAX)
      for t in self._dpn.reachable(i):
        is_t = s.eq(self._vs_trans[i], s.num(t["id"]))
        e = s.ite(is_t, s.num(len(t["write"]) + 1), e)
      return e
    
    def syncost(i,j):
      e = s.real(MAX)
      for (is_t, penalty) in self.sync_costs_fixed_order(trace, i, j):
        e = s.ite(is_t, penalty, e)
      return e
  
    self._penalties = (lcost, mcost, syncost, drop_cost)
    return self.edit_distance_parametric(trace, self._penalties)
  

  def edit_distance_fitness(self, trace):
    #print(trace)
    if not trace.has_uncertain_time():
      return self.edit_distance_fitness_fixed_order(trace)
    else:
      return self.edit_distance_fitness_var_order(trace)


  def print_distance_matrix(self, model):
    print("\nDISTANCES:")
    n = len(self._vs_dist)
    m = len(self._vs_dist[0])
    for j in range(0, m):
      d = ""
      for i in range(0, n):
        fval = "%.2f" % model.eval_real(self._vs_dist[i][j])
        is_int = float(fval) - int(float(fval)) == 0
        if is_int:
          fval = str(int(float(fval)))
        # k = model.eval_int(self._vs_move_type[i][j])
        sort = "z" if  i < n-1 and model.eval_bool(self._silents[i]) else \
          "l" if model.eval_bool(self._vs_log_move[i][j]) else \
          "m" if model.eval_bool(self._vs_mod_move[i][j]) else \
          "d" if j > 0 and model.eval_bool(self._vs_drop[j-1]) else \
          "s" if j < m-1 and model.eval_bool(self._vs_syn_move[i][j]) else "?"
        d = d + pad_to(fval+ sort, 5)  + " "
      print(d)


  def decode_ordering(self, trace, model):
    if trace.has_uncertain_time():
      ord_trace = []
      traceid_map = dict([ (e._id, e) for e in trace._events ])
      for j in range(0, len(trace)):
        id = model.eval_int(self._vs_trace[j])
        uevent = traceid_map[id]
        uevent.fix_time(model.eval_real(self._vs_time[id]))
        ord_trace.append(uevent)
      ord_trace = UncertainTrace(ord_trace)
    else:
      ord_trace = trace
    return ord_trace


  def decode_alignment(self, trace, model):
    m = len(trace)
    vs_dist = self._vs_dist
    run_length = self.decode_run_length(model)
    distance = model.eval_real(vs_dist[run_length][len(trace)])
    run = self.decode_process_run(model, run_length)
    (markings, transitions, valuations) = run

    ord_trace = self.decode_ordering(trace, model)
    #self.print_distance_matrix(model)

    i = run_length # n
    j = len(ord_trace) # m
    (lcost, mcost, syncost, pcost) = self._penalties
    alignment = [] # array mapping instant to one of {"log", "model","parallel", "skip"}
    drops = [ model.eval_bool(v) for v in self._vs_drop ]
    #print("drops", drops)
    logmoves = [[ model.eval_bool(self._vs_log_move[i][j]) \
      for j in range(0, len(trace)+1)] for i in range(0, len(self._vs_log_move))]
    modmoves = [[ model.eval_bool(self._vs_mod_move[i][j]) \
      for j in range(0, len(trace)+1)] for i in range(0, len(self._vs_mod_move))]
    #print("silents", [ model.eval_bool(v) for v in self._silents ])
    while i > 0 or j > 0:
      if model.eval_bool(self._vs_log_move[i][j]):
        alignment.append("log")
        j -= 1
      elif model.eval_bool(self._vs_mod_move[i][j]):
        if not model.eval_bool(self._silents[i-1]):
          alignment.append("model")
        i -= 1
      elif drops[j-1]:
        alignment.append("drop")
        ord_trace.drop(j-1) # modify ordtrace to skip this guy
        j -= 1
      else:
        assert(model.eval_bool(self._vs_syn_move[i][j]))
        alignment.append("parallel")
        ord_trace[j-1].fix_label(transitions[i-1][1]) # modify ordtrace
        ord_trace[j-1].fix_determinacy()
        ord_trace[j-1].fix_data(valuations[i])
        i -= 1
        j -= 1
     
    alignment.reverse()
    return {
      "run": {
        "transitions": transitions,
        "markings":    markings, 
        "valuations":  valuations
      },
      "trace": [ e.project() for e in ord_trace],
      "alignment":   alignment,
      "cost":    distance
    }
    
        
