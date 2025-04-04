from functools import reduce
from itertools import groupby

from dpn.expr import Expr
from utils import VarType

class Encoding:

  def __init__(self, dpn, solver, step_bound):
    self._dpn = dpn
    self._solver = solver
    self._step_bound = step_bound
    self._vs_data = self.data_vars()
    self._vs_mark = self.marking_vars()
    self._vs_trans = self.trans_vars()
    self._run_length = self._solver.intvar("run_length")

  def step_bound(self):
    return self._step_bound

  def solver(self):
    return self._solver

  def dpn(self):
    return self._dpn

  def data_vars(self):
    varwrite = self._dpn.var_write_reach()
    vs = self._dpn.variables()

    
    def init(v):
      val = v["initial"] if "initial" in v else 0
      type = VarType.from_java(v["type"])
      return self._solver.real(val) if type == VarType.real else \
        self._solver.num(val)

    def create_var(v, i):
      name = "_" + v["name"] + "_" + str(i)
      type = VarType.from_java(v["type"])
      return self._solver.realvar(name) if type == VarType.real else \
        self._solver.intvar(name)

    init = [(v["name"], init(v)) for v in vs]
    vvars = [ dict([ (vn, val) for (vn,val) in init ]) ]
    # FIXME: beforehand all vars were reals. can be faster
    # init = [(v["name"], v["initial"] if "initial" in v else 0) for v in vs]
    # vvars = [ dict([ (vn, self._solver.num(val)) for (vn,val) in init ]) ]
    # create_var = lambda v, i: self._solver.realvar("_" + v["name"] + str(i))

    
    for i in range(1, self._step_bound + 1):
      xis = {} # dictionary mapping data variable name to SMT variable
      for v in vs:
        n = v["name"]
        # optimization:
        # if no transition writing variable v is reachable in i steps, v cannot
        # be written, so take respective variable of instant i - 1
        xis[n] = create_var(v,i)# if n in varwrite[i-1] else vvars[i-1][n]
      vvars.append(xis)
    return vvars

  # returns list mvs such that mvs[i] is dictionary mapping place id to integer
  # variable for number of tokens n, i.e. mvs[i][place_id] = n
  # optimization: marking variables are boolean if dpn one-bounded, else integer
  def marking_vars(self):
    s = self._solver
    def mvar(i, id):
      name = "marked_" + str(i) + "_" + str(id)
      return s.boolvar(name) if self._dpn.is_one_bounded() else s.intvar(name)
    # create dictionary of variables for given instant i
    mvs = lambda i: dict([(p["id"], mvar(i,p["id"])) for p in self._dpn.places()])
    # create dictionaries of variables for all instants i
    return [ mvs(i) for i in range(0, self._step_bound+1) ]

  # create integer variable to capture transition for every instant
  def trans_vars(self):
    name = lambda i: "trans" + str(i)
    return [ self._solver.intvar(name(i)) for i in range(0, self._step_bound) ]

  # create (step_bound x trace_len) integer variables for edit distance
  def edit_distance_vars(self, trace_len):
    s = self._solver
    def var(i, j):
      return s.intvar("d" + str(i) + "_" + str(j)) if i > 0 or j>0 else s.real(0)
    return [[var(i,j) \
      for j in range(0, trace_len+1)] for i in range(0, self._step_bound+1)]

  # create variables for move types
  def move_vars(self, trace_len, pre):
    s = self._solver
    var = lambda i, j: s.boolvar("move" + pre + str(i) + "_" + str(j))
    return [[var(i,j) \
      for j in range(0, trace_len+1)] for i in range(0, self._step_bound+1)]

  # return pair of edit distance expression and side constraints
  def prepare_edit_distance(self, len_trace):
    self._vs_dist = self.edit_distance_vars(len_trace)
    #self._vs_syn_move = self.move_vars(len_trace, "s")
    self._vs_log_move = self.move_vars(len_trace, "l")
    self._vs_mod_move = self.move_vars(len_trace, "m")
    
  # fix initial state; initial data is fixed in data variable initialization
  def initial_state(self):
    s = self._solver
    mvs = self._vs_mark
    mcount = [(p["id"], p["initial"] if "initial" in p else 0) \
      for p in self._dpn.places()]
    if self._dpn.is_one_bounded():
      marking0 = [ mvs[0][p] if c > 0 else s.neg(mvs[0][p]) for (p,c) in mcount]
    else:
      marking0 = [ s.eq(mvs[0][p], s.num(c)) for (p, c) in mcount ]
    return s.land(marking0)

  # all transition variables trans_vars[i] have as value a transition id that is
  # reachable in i steps in the net
  def transition_range(self):
    s = self._solver
    dpn = self._dpn
    tvs = self._vs_trans
    
    def rng(i, v):
      reach = dpn.reachable(i)
      if len(reach) > 0:
        return s.lor([s.eq(v, s.num(t["id"])) for t in reach])
      else:
        return s.le(self._run_length, s.num(i))
    rng_constr = [rng(i, v) for (i, v) in enumerate(tvs)]
    # optimization: the following serves only for symmetry breaking:
    # if transition is tau (i.e., final filler transition) then so is the next
    tau_transs = [t for t in dpn.transitions() if not t["label"]]
    is_tau = lambda v: s.lor([s.eq(v, s.num(t["id"])) for t in tau_transs])
    butlast = range(0, len(tvs) - 1)
    tau_constr = [ s.implies(is_tau(tvs[i]), is_tau(tvs[i+1])) for i in butlast]
    # FIXME: assess usefulness of the following
    """
    unique = [ s.implies(s.eq(v, s.num(tid)), s.neg(s.eq(w, s.num(tid)))) \
      for tid in self._dpn.single_occurrence_transitions() \
      for (i, v) in enumerate(tvs) for (j, w) in enumerate(tvs) if i < j \
      if tid in dpn.reachable(i) ]
    follows = [ s.implies(s.eq(tvs[i], s.num(tid)), s.neg(s.eq(tvs[i+1], s.num(tnextid))))\
      for i in range (0,len(tvs)-1) \
      for (tid, tnextid) in dpn.directly_follows_transitions() \
      if tid in dpn.reachable(i) ]
    """
    #print("follow", dpn.directly_follows_transitions())
    #print("unique", dpn.single_occurrence_transitions())
    return s.land(rng_constr + tau_constr)

  # the last marking is final
  def final_state(self):
    s = self._solver
    places = self._dpn.places()
    mvs = self._vs_mark
    bound = self._step_bound
    self._finals = [s.boolvar("final"+str(i)) for i in range(0, bound + 1)]

    if self._dpn.is_one_bounded():
      fmark = [ p["id"] for p in places if "final" in p ]
      return s.land([ mvs[bound][p] for p in fmark ])
    else:
      fmark = [ (p["id"], p["final"] if "final" in p else 0) for p in places ]
      final = lambda i: s.land([ s.eq(mvs[i][p], s.num(c)) for (p,c) in fmark ])
      if self._dpn.has_final_places():
        return final(bound)
      else:
        rl = self._run_length
        fs = [ s.iff(v, final(i)) for (i,v) in enumerate(self._finals) ]
        rls = [ s.implies(s.eq(rl, s.num(i)), final(i)) \
          for (i,v) in enumerate(self._finals) ]
        return s.land(fs + rls + [s.lor(self._finals)])

    
  # token game for transition t and instant i (case of unbounded net)
  def token_game_unbounded(self, t, i):
    s = self._solver
    dpn = self._dpn
    mvars = self._vs_mark
    pre = [ e["source"] for e in dpn.arcs() if e["target"] == t["id"] ]
    post = [ e["target"] for e in dpn.arcs() if e["source"] == t["id"] ]
    # count multiplicities of places in pre and post
    mpre = dict([ (p, len(list(g))) for (p,g) in groupby(pre)])
    mpost = dict([ (p, len(list(g))) for (p,g) in groupby(post)])
    # partition places in only pre, only post, both, and neither
    pre_not_post = [ (p,c) for (p,c) in mpre.items() if not p in mpost ]
    post_not_pre = [ (p,c) for (p,c) in mpost.items() if not p in mpre ]
    pre_and_post = [ (p, mpost[p] - c) for (p,c) in mpre.items() if p in mpost ]
    others = [ p["id"] for p in dpn.places() if not (p["id"] in post+pre) ]
    # transition t is enabled
    pre_enabled = [ s.ge(mvars[i][p], s.num(c)) for (p, c) in mpre.items() ]
    # token game
    pre_change = [ s.eq(mvars[i][p], s.plus(mvars[i+1][p], s.num(c))) \
      for (p, c) in pre_not_post ]
    post_change = [ s.eq(mvars[i+1][p], s.plus(mvars[i][p], s.num(c))) \
      for (p, c) in post_not_pre]
    both_change = [ s.eq(s.minus(mvars[i+1][p], mvars[i][p]), s.num(d)) \
      for (p,d) in pre_and_post ]
    stay_same = [ s.eq(mvars[i][p], mvars[i+1][p]) for p in others ]
    all = pre_enabled + pre_change + post_change + both_change + stay_same
    return s.land(all)

  # token game for transition t and instant i (case of unbounded net)
  def token_game_half_bounded(self, t, i):
    s = self._solver
    dpn = self._dpn
    mvars = self._vs_mark
    pre = [ e["source"] for e in dpn.arcs() if e["target"] == t["id"] ]
    post = [ e["target"] for e in dpn.arcs() if e["source"] == t["id"] ]
    # partition places in only pre, only post, both, and neither
    pre_not_post = [ p for p in pre if not p in post ]
    others = [ p["id"] for p in dpn.places() if not (p["id"] in post+pre) ]
    # transition t is enabled
    pre_enabled = [ mvars[i][p] for p in pre ]
    # token game
    pre_change = [ s.neg(mvars[i+1][p]) for p in pre_not_post ]
    post_change = [ mvars[i+1][p] for p in post ]
    stay_same = [ s.iff(mvars[i][p], mvars[i+1][p]) for p in others ]
    all = pre_enabled + pre_change + post_change + stay_same
    return s.land(all)

  # token game for transition t and instant i (case of one-bounded net)
  def token_game_1bounded(self, t, i):
    s = self._solver
    dpn = self._dpn
    mvars = self._vs_mark
    pre = [ e["source"] for e in dpn.arcs() if e["target"] == t["id"] ]
    post = [ e["target"] for e in dpn.arcs() if e["source"] == t["id"] ]
    assert(len(pre) == 1 and len(post) == 1)
    p1 = pre[0]
    p2 = post[0]
    # partition places in only pre, only post, both, and neither
    others = [ p["id"] for p in dpn.places() if not (p["id"] in post + pre) ]
    if p1 == p2:
      pre_post = [ mvars[i][p1], mvars[i+1][p1] ]
    else:
      pre_post = [ mvars[i][p1], s.neg(mvars[i+1][p1]), mvars[i+1][p2] ]
    stay_same = [ s.neg(mvars[i+1][p]) for p in others ]
    return s.land(pre_post + stay_same)

  # encode data constraints for transition t and instant i
  def data_constraints(self, t, i):
    s = self._solver
    dvars = self._vs_data
    vs = [v["name"] for v in self._dpn.variables()]
    sub_prime = [ (x + "'", v) for (x, v) in dvars[i+1].items() ]
    sub = dict(list(dvars[i].items()) + sub_prime)
    has_constr = "constraint" in t
    # encode guard constraint
    trans_constr = t["constraint"].toSMT(s,sub) if has_constr else s.true()
    # inertia
    keep = [v for v in vs if not v in t["write"] ] if "write" in t else vs
    keep_constr = [s.eq(dvars[i][v], dvars[i+1][v]) for v in keep \
      if not s.are_equal_expr(dvars[i][v], dvars[i+1][v]) ] # skip if vars equal
    return s.land([trans_constr] + keep_constr)

  def transition_constraints(self):
    s = self._solver
    # conditions on transition at instant i being t
    def step(i, t):
      tvar = self._vs_trans[i]
      mark_chng = self.token_game_1bounded(t,i) if self._dpn.is_one_bounded() \
        else self.token_game_unbounded(t, i)
      data_chng = self.data_constraints(t, i)
      return s.implies(s.eq(tvar,s.num(t["id"])), s.land([mark_chng,data_chng]))
    
    # big conjunction over all instants and all possible transitions
    return s.land([ step(i, t) \
      for i in range(0, self._step_bound) for t in self._dpn.reachable(i)])

  # auxiliary for edit distance encoding below:
  # returns pairs (is_t, penalty expression) for all transitions t
  def sync_step(self, trace, i, j):
    subst_prime = dict([ (x, v) for (x, v) in self._vs_data[i+1].items() ])
    s = self._solver

    vartypes = dict([ (v["name"], VarType.from_java(v["type"])) for v in self._dpn._variables ])

    def write_diff(t):
      diff = s.num(0)
      for x in t["write"]:
        # FIXME: perhaps no penalty should be given if a write value is not
        # mentioned in the trace but keeping the value beforehand is ok
        if x not in trace[j]["valuation"]:
          diff = s.inc(diff) 
        else:
          val = Expr.numval(trace[j]["valuation"][x])
          valexpr = s.real(val) if vartypes[x] == VarType.real else s.num(val)
          diff = s.ite(s.eq(subst_prime[x], valexpr), diff, s.inc(diff))
      return (diff, len(t["write"]) > 0)

    return [ (s.eq(self._vs_trans[i], s.num(t["id"])), write_diff(t)) \
      for t in self._dpn.reachable(i) \
      if "label" in t and t["label"] == trace[j]["label"] ]


  # return pair of edit distance expression and side constraints
  def edit_distance(self, trace):
    delta = self._vs_dist
    vs_log = self._vs_log_move
    vs_mod = self._vs_mod_move
    syn_move = lambda i, j: s.neg(s.lor([vs_mod[i][j], vs_log[i][j]]))
    n = self._step_bound
    m = len(trace)
    s = self._solver
    dpn = self._dpn
    vs_trans = self._vs_trans
    vs_data = self._vs_data
    etrans = [(t["id"], t) for t in dpn.transitions()]
    trans_dict = dict(etrans)
    vars = dpn.variables()    

    # write cost of a transition (to determine model step penalty)
    # optimization: more efficient to use variables instead of just constants
    def wcostint(t):
      write_t = len(t["write"]) if "write" in t else 0
      return 0 if t["invisible"] else 1 + write_t # unless silent: #writes + 1
    wcs = [(t["id"], wcostint(t)) for t in dpn.transitions() ]
    per_cost = [ (c, [tid for (tid,c2) in wcs if c==c2]) for (_,c) in wcs ]
    wcostvars = [s.intvar("wcost"+str(t["id"])) for t in dpn.transitions() ]
    ws = [ s.eq(v, s.num(wcostint(t))) \
      for (v, t) in zip(wcostvars, dpn.transitions()) ]
    wcostd = dict([ (t["id"], v) for (t,v) in zip(dpn.transitions(), wcostvars)])
    
    def async_step(i, j):
      return [ (s.eq(vs_trans[i], s.num(t["id"])), wcostd[t["id"]]) \
        for t in dpn.reachable(i) \
        if not t["invisible"] and t["label"] != trace[j]["label"] ]
    
    # write costs for vs_trans[i ], alternative over all transitions
    def wcost(i):
      var = vs_trans[i]
      reach = dpn.reachable(i)
      return reduce(lambda c, wc: \
        s.ite(s.lor([s.eq(var, s.num(tid)) for tid in wc[1] if tid in reach]), \
          s.num(wc[0]), c), per_cost[1:], s.num(per_cost[0][0]))
    wcosts = [s.intvar("wcosti"+str(i)) for i in range(0,n) ]
    ws += [ s.eq(v, wcost(i)) for (i,v) in enumerate(wcosts) ]

    def is_silent(i): # transition i is silent
      return s.lor([ s.eq(vs_trans[i], s.num(id)) \
        for (id, t) in etrans if t in dpn.reachable(i) and t["invisible"] ])
    
    silents2 = [ is_silent(i) for i in range(0,n) ]
    self._silents = [s.boolvar("silent"+str(i)) for i in range(0,n) ]
    ss = [ s.iff(v,e) for (v,e) in zip(self._silents, silents2)]

    # delta[i][j] represents the edit distance of transition sequence up to
    # including i, and the log up to including j
    # optimization: constraints of form delta[i+1][j+1] = e are equivalent to
    # delta[i+1][j+1] >= e due to minimization. replaced some for performance
    # base cases
    # 1. all intermediate distances delta[i][j] are non-negative
    non_neg = [s.ge(delta[i][j], s.num(0))\
      for i in range(0,n+1) for j in range(0,m+1)]
    # 2. if the ith transition is not silent, delta[i+1][0] = delta[i][0] + wcost
    #    where wcost is the writing cost of the ith transition in the model
    incdelta0 = [s.intvar("incd0"+str(i)) for i in range(0,n) ]
    bm = [ s.eq(incdelta0[i], s.plus(delta[i][0], wcosts[i])) for i in range(0,n)]
    base_model = [ s.implies(s.neg(self._silents[i]), \
      s.ge(delta[i+1][0], incdelta0[i])) for i in range(0,n)]
    # 3. delta[0][j+1] = (j + 1)
    base_log = [ s.eq(delta[0][j+1], s.num(j + 1)) for j in range(0,m) ]
    # 4. if the ith step in the model and the jth step in the log have the
    #    the same label,  delta[i+1][j+1] >= delta[i][j] + penalty, where
    #    penalty accounts for the data mismatch (possibly 0)
    sync_step = []
    for i in range(0,n):
      for j in range(0,m):
        trans_options = self.sync_step(trace, i, j)
        if len(trans_options) == 0:
          sync_step.append(s.neg(syn_move(i+1,j+1)))
        else:
          sync_step += [ s.implies(is_t, \
            s.ge(delta[i+1][j+1], \
              s.plus(penalty, delta[i][j]) if has_penalty else delta[i][j])) \
                for (is_t, (penalty, has_penalty)) in trans_options ]

    # 5. the ith step in the model and the jth step in the log have different 
    #    labels: delta[i+1][j+1] is minimum of delta[i][j+1], delta[i+1][j]
    #    plus respective penalty values
    side_constr = []
    for i in range(0,n):
      reachable_labels = set([ t["label"] for k in range(i, n) for t in dpn.reachable(k)])
      for j in range(0,m):
        # side constraints on log step (vertical move in matrix)
        log_step = s.implies(vs_log[i+1][j+1], \
          s.ge(delta[i+1][j+1], s.inc(delta[i+1][j])))
        side_constr.append(log_step)
        # side constraints on model step (horizontal move in matrix)
        if trace[j]["label"] in reachable_labels or j == 0 or j == m-1:
          for (is_t, penalty) in async_step(i, j):
            mstep = s.plus(penalty, delta[i][j+1])
            mod_step = s.implies(vs_mod[i+1][j+1], s.ge(delta[i+1][j+1], mstep))
            imp = s.implies(is_t, s.land([mod_step,
              s.lor([ vs_mod[i+1][j+1], vs_log[i+1][j+1]])]))
            side_constr.append(imp)
        else:
          side_constr.append(vs_log[i+1][j+1])

    # symmetry breaking: enforce log steps before model steps
    # do not enforce at border: would be unsound
    for i in range(2,n-1):
      for j in range(3,m-1):
        c = s.implies(vs_mod[i][j-1], s.neg(vs_log[i][j]))
        side_constr.append(c)
    
    # 6. if the ith step in the model is silent, delta[i+1][j] = delta[i][j],
    #    that is, silent transitions do not increase the distance
    silent = [ s.implies(s.land([vs_mod[i+1][j], self._silents[i]]), 
      s.eq(delta[i+1][j], delta[i][j])) \
      for i in range(0,n) for j in range(0,m+1) ]
    
    # run length, only relevant for multiple tokens/ no final places
    rl = [s.ge(self._run_length, s.num(0)), s.ge(s.num(n), self._run_length)]
    
    if self._dpn.has_final_places():
      min_expr = delta[n][m]
    else:
      min_expr = delta[0][m]
      for i in range(1,n+1):
        min_expr = s.ite(s.eq(self._run_length, s.num(i)), delta[i][m],min_expr)

    constraints = non_neg + base_model + base_log + sync_step + side_constr + \
      silent + ss + ws + bm + rl
    return (min_expr, s.land(constraints))


  def decode_process_run(self, model, run_length):
    dpn = self._dpn
    places = dict([ (p["id"], p) for p in dpn.places() ])
    transs = dict([ (t["id"], t) for t in dpn.transitions() ])
    tlabel = lambda i: "tau" if not transs[i]["label"] else transs[i]["label"]
    vs_data = self._vs_data
    vs_mark = self._vs_mark
    valuations = [] # array mapping instant to valuation
    markings = [] # array mapping instant to dictionary mapping place to count
    transitions = [] # array mapping instant to transition label
    eval_mark = lambda v: int(model.eval_bool(v)) \
      if self._dpn.is_one_bounded() else model.eval_int(v)

    for i in range(0, run_length + 1):
      val = [ (x, model.eval_real(v)) for (x,v) in vs_data[i].items()]
      valuations.append(dict(val))
      mark = [(places[p]["id"],eval_mark(c)) for (p,c) in vs_mark[i].items()]
      markings.append(dict(mark))
      if i < run_length:
        tid = model.eval_int(self._vs_trans[i])
        if not self._dpn.is_silent_final_transition(tid):
          transitions.append((tid, tlabel(tid)))
    return (markings, transitions, valuations)

  def decode_run_length(self, model):
    if self._dpn.has_final_places():
      return self._step_bound
    else:
      return model.eval_int(self._run_length)

  def print_distance_matrix(self, model, real = False):
    print("\nDISTANCES:")
    for j in range(0, len(self._vs_dist[0])):
      d = ""
      for i in range(0, len(self._vs_dist)):
        s = str(model.eval_int(self._vs_dist[i][j]))
        d = d + " " + (s if len(s) == 2 else (" "+s))
      print(d)

  def print_move_type_matrix(self, model):
    print("MOVE TYPES:")
    for j in range(0, len(self._vs_dist[0])):
      d = ""
      for i in range(0, len(self._vs_dist)):
        s = "L" if model.eval_bool(self._vs_log_move[i][j]) else \
          "M" if model.eval_bool(self._vs_mod_move[i][j]) else "S"
        d = d + " " + (s if len(s) == 2 else (" "+s))
      print(d)

  def decode_alignment(self, trace, model):
    m = len(trace)
    vs_dist = self._vs_dist
    transs = dict([ (t["id"], t) for t in self._dpn.transitions() ])
    run_length_dec = self.decode_run_length(model)
    distance = model.eval_int(vs_dist[run_length_dec][len(trace)])
    run = self.decode_process_run(model, run_length_dec)
    (markings, transitions, valuations) = run
    run_length = len(transitions)
    # self.print_distance_matrix(model)
    # self.print_move_type_matrix(model)

    i = run_length # self._step_bound # n
    j = len(trace) # m
    alignment = [] # array mapping instant to one of {"log", "model","parallel"}
    while i > 0 or j > 0:
      dist = model.eval_int(vs_dist[i][j])
      if j == 0 or (i > 0 and model.eval_bool(self._silents[i-1])):
        if not self._dpn.is_silent_final_transition(transitions[i-1][0]):
          alignment.append("model")
        i -= 1
      elif i == 0:
        alignment.append("log")
        j -= 1
      elif transitions[i-1][1] == trace[j-1]["label"]:
        alignment.append("parallel")
        i -= 1
        j -= 1
      else:
        dist_log = model.eval_int(vs_dist[i][j-1]) + 1
        tmodel = transs[transitions[i-1][0]]
        dist_model = model.eval_int(vs_dist[i-1][j]) + len(tmodel["write"]) + 1
        # assert(dist == dist_log or dist == dist_model)
        if dist == dist_log:
          alignment.append("log")
          j -= 1
        else:
          alignment.append("model")
          i -= 1
    alignment.reverse()
    return {
      "run": {
        "transitions": transitions,
        "markings":    markings, 
        "valuations":  valuations
      },
      "alignment":   alignment,
      "cost":        distance
    }
  