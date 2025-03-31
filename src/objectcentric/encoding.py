from functools import reduce

from dpn.expr import Expr
from utils import VarType

# TODO: if there are place/inscription types that contain ONLY data types, the
#       current encoding does not work (need to add dummy black token for that)

class Encoding():
  def __init__(self, solver, net, trace):
    self._solver = solver
    self._net = net
    self._trace = trace
    self._objects = trace.get_objects()
    self._objects_by_type = self._net.objects_by_type(self._objects)
    net.compute_reachable(trace)
    self._step_bound = net.step_bound(trace)
    oids = [ (n, id) for os in self._objects_by_type.values() for (n, id) in os]
    self._ids_by_object_name = dict(oids)
    self._object_name_by_id = dict([(id,n) for (n, id) in oids])
    self._tokens_by_color = self._net.tokens_by_color(self._objects) # w/o data
    self._max_objs_per_trans = \
      self._net.get_max_objects_per_transition(self._objects)
    # cache encoding parts
    self._consumed_token_cache = {}
    self._produced_token_cache = {}

  def get_solver(self):
    return self._solver

  def get_step_bound(self):
    return self._step_bound

  def initial_state(self, fixed_objects):
    s = self._solver
    if fixed_objects:
      mvars0 = self._marking_vars[0]
      cs = []
      for (id, name) in self._object_name_by_id.items():
        for p in self._net._places:
          if not ("initial" in p and p["initial"]): # no tokens
            cs += [s.neg(v) for v in mvars0[p["id"]].values()]
          else: # all tokens of this color
            assert(len(p["color"]) == 1)
            cs += [v for v in mvars0[p["id"]].values()]
      return s.land(cs)
    else:
      # initial marking is empty marking, nu transitions are assumed to create objects
      mvars0 = [v for vs in self._marking_vars[0].values() for v in vs.values()]
      return s.land([s.neg(v) for v in mvars0])

  def final_state_after_step(self, j):
    last_marking = self._marking_vars[j]
    constraints = []
    s = self._solver
    for p in self._net._places:
      p_is_final = bool("final" in p and p["final"])
      tokens_in_place = []
      for t in self._tokens_by_color[p["color"]]:
        tok_placed = last_marking[p["id"]][t]
        tokens_in_place.append(tok_placed if p_is_final else s.neg(tok_placed))
      if p_is_final: # final places contain some token
        constraints.append(s.lor(tokens_in_place))
      else: # non-final places contain no token
        constraints.append(s.land(tokens_in_place))
    return s.land(constraints)

  def final_state(self):
    # FIXME how to specify final marking?
    # currently we only require that places marked as final have some token
    s = self._solver
    run_length = lambda j: s.eq(self._run_length_var, s.num(j))
    return s.lor([ s.land([run_length(j), self.final_state_after_step(j)]) \
      for j in range(0,self._step_bound+1)])
  
  # Returns formula expressing whether token tok is involved in the firing of
  # transition t at step j, where the token is
  # - consumed from place p if incoming is True, and
  # - produced in place p if incoming is False
  def is_fired_token(self, p, t, tok, j, incoming):
    s = self._solver
    ovars = self._object_vars
    obj_params = self._net.object_inscriptions_of_transition(t, self._objects)
    params = [x for x in obj_params if x["place"] == p["id"] and \
      x["incoming"] == incoming]
    eqs = []
    # FIXME use self._net.get_inscription
    inscription = next(a["inscription"] for a in self._net._arcs \
      if (incoming and a["source"] == p["id"] and a["target"] == t["id"]) or \
        (not incoming and a["target"] == p["id"] and a["source"] == t["id"]))
    params_for_insc = []
    for (pname, _) in inscription:
      params_for_insc.append([x for x in params if x["name"] == pname])
    # loop over pairs of token element and parameter name
    for (obj, params) in zip(tok, params_for_insc):
      objid = self._ids_by_object_name[obj]
      inst2token = [ s.eq(ovars[j][p["index"]], s.num(objid)) for p in params]
      eqs.append(s.lor(inst2token))
    return s.land(eqs)

  # Returns formula expressing whether token tok is consumed from place p in the
  # firing of transition t at step j. Formula is cached.
  def is_consumed_token(self, p, t, tok, j):
    keytuple = (p["id"], t["id"], tok, j)
    if keytuple in self._consumed_token_cache:
      return self._consumed_token_cache[keytuple][0]
    
    expr = self.is_fired_token(p, t, tok, j, True)
    index = len(self._consumed_token_cache)
    var = self._solver.boolvar("cons_token" + str(index))
    self._consumed_token_cache[keytuple] = (var, expr)
    return var

  # Returns formula expressing whether token tok is produced in place p in the
  # firing of transition t at step j. Formula is cached.
  def is_produced_token(self, p, t, tok, j):
    keytuple = (p["id"], t["id"], tok, j)
    if keytuple in self._produced_token_cache:
      return self._produced_token_cache[keytuple][0]
    
    expr = self.is_fired_token(p, t, tok, j, False)
    index = len(self._produced_token_cache)
    var = self._solver.boolvar("prod_token" + str(index))
    self._produced_token_cache[keytuple] = (var, expr)
    return var

  def moving_tokens(self):
    s = self._solver
    mvars = self._marking_vars

    def trans_j_consumed(t, j):
      cnstr = []
      for p in self._net.pre(t):
        for tok in self._tokens_by_color[p["color"]]:
          pid = p["id"] # the source
          is_self_loop = pid in [ p["id"] for p in self._net.post(t)]
          marked = s.land([mvars[j][pid][tok], s.neg(mvars[j+1][pid][tok])]) \
            if not is_self_loop else mvars[j][pid][tok]
          # if the token is consumed, the marking changes accordingly
          is_consumed = self.is_consumed_token(p, t, tok, j)
          cnstr.append(s.implies(is_consumed, marked))
          # if there is an exact sync arc, also the reversed implication holds
          if self._net.is_exact_sync_arc(p,t):
            cnstr.append(s.implies(marked, is_consumed))

      return s.land(cnstr)

    def trans_j_produced(t, j):
      cnstr = []
      for p in self._net.post(t):
        for tok in self._tokens_by_color[p["color"]]:
          marked = mvars[j+1][p["id"]][tok]
          cnstr.append(s.implies(self.is_produced_token(p, t, tok, j), marked))
      return s.land(cnstr)

    run_length_lt = lambda j: s.lt(s.num(j), self._run_length_var)
    jth_trans_is = lambda j, tid: \
      s.land([s.eq(self._transition_vars[j], s.num(tid)), run_length_lt(j)])

    # demand that chosen transition must consume and produce as intended
    cstr = [s.implies(jth_trans_is(j, t["id"]), \
        s.land([trans_j_consumed(t, j), trans_j_produced(t, j)])) \
      for j in range(0, self._step_bound) \
      for t in self._net._transitions]
    return s.land(cstr)

  def remaining_tokens(self):
    s = self._solver
    tvars = self._transition_vars
    mvars = self._marking_vars

    def moved_token(p, tok, j):
      consumed_by = lambda t: self.is_consumed_token(p,t,tok,j)
      produced_by = lambda t: self.is_produced_token(p,t,tok,j)
      is_trans = lambda t: s.eq(tvars[j],s.num(t["id"]))
      consumed = [ s.land([consumed_by(t), is_trans(t)]) \
        for t in self._net.post_trans(p)]
      produced = [ s.land([produced_by(t), is_trans(t)]) \
        for t in self._net.pre_trans(p)]
      return s.lor(consumed + produced) 

    cnstr = []
    for j in range(0, self._step_bound):
      for p in self._net._places:
        pid = p["id"]
        for tok in self._tokens_by_color[p["color"]]:
          moved = moved_token(p, tok, j)
          marking_stays = s.iff(mvars[j][pid][tok], mvars[j+1][pid][tok])
          cnstr.append(s.lor([moved, marking_stays]))
    return s.land(cnstr)


  # ensure that transitions use objects of correct type
  def object_types(self):
    s = self._solver
    tvars = self._transition_vars
    ovars = self._object_vars
    max_objs = self._max_objs_per_trans
    cache_cstr = []
    obj_disj_cache = {}
    objs_by_type = self._net.objects_by_type(self._objects)
    
    # disjunction expressing which objects can instantiate an object param at j
    def cache_obj_disj(param, j):
      key = (j, param["type"], param["needed"], param["index"])
      if not key in obj_disj_cache:
        param_disj = [ s.eq(ovars[j][param["index"]], s.num(id)) \
          for (obj_name, id) in objs_by_type[param["type"]]]
        if not param["needed"]:
          param_disj.append(s.eq(ovars[j][param["index"]], s.num(-1)))
        #return s.lor(param_disj) # without caching
        ojvar = s.boolvar("obj_cache_%d" % (len(obj_disj_cache)))
        obj_disj_cache[key] = ojvar
        cache_cstr.append(s.implies(ojvar, s.lor(param_disj)))
      return obj_disj_cache[key]

    def trans_j_constraint(t, j):
      params = self._net.object_params_of_transition(t, self._objects)
      # filter out parameters that are data variables
      obj_params = [p for p in params if p["type"] not in self._net._data_types]
      obj_conj = [ cache_obj_disj(param, j) for param in obj_params ]
      for pidx in range(len(obj_params), max_objs): # unused object indices
        obj_conj.append(s.eq(ovars[j][pidx], s.num(-1)))
      return s.land(obj_conj)
    
    cstr = [s.implies(s.eq(tvars[j], s.num(t["id"])), trans_j_constraint(t,j)) \
      for j in range(0, self._step_bound) \
      for t in self._net._transitions] # FIXME reachable does not suffice, why?
    return s.land(cstr+cache_cstr)
  

  # ensure that objects substituted for nu inscriptions do not occur in marking
  def freshness(self):
    s = self._solver
    tvars = self._transition_vars
    ovars = self._object_vars
    mvars = self._marking_vars

    def not_in_marking(oid, j):
      # object with id k is not in marking at time j
      oname = self._object_name_by_id[oid]
      constraints = []
      mvarsj = mvars[j]
      for p in self._net._places:
        tokens = [ t for t in self._tokens_by_color[p["color"]] if oname in t ]
        for t in tokens:
          constraints.append(s.neg(mvarsj[p["id"]][t]))
      return self._solver.land(constraints)

    # variables for not_in_marking expressions, which are used multiple times
    not_marked = [[s.boolvar("not_marked_%d_%d" % (j, oid)) \
      for oid in self._object_name_by_id.keys()] \
      for j in range(0, self._step_bound)]
    # use implies instead of iff as variable is only used positively
    not_marked_constr = [ s.implies(not_marked[j][oid],not_in_marking(oid, j)) \
      for oid in self._object_name_by_id.keys() \
      for j in range(0, self._step_bound) ]

    def nutrans_constraint(t, j):
      obj_params = self._net.object_params_of_transition(t, self._objects)
      constraints = []
      for param in obj_params:
        k = param["index"]
        # kth object parameter of transition t
        if not "nu" in param["name"]:
          continue
        # marking j is before transition j
        imps = [s.implies(s.eq(ovars[j][k], s.num(id)), not_marked[j][id]) \
          for (obj_name, id) in self._objects_by_type[param["type"]]]
        constraints += imps
      return s.land(constraints)

    run_length_le = lambda j: s.le(s.num(j), self._run_length_var)
    cstr = [s.implies(
      s.land([s.eq(tvars[j], s.num(t["id"])), run_length_le(j)]),
      nutrans_constraint(t,j)) \
      for j in range(0, self._step_bound) \
      for t in self._net.nu_transitions() ]
    return s.land(cstr + not_marked_constr)

  # all transition variables trans_vars[i] have as value a transition id that is
  # reachable in i steps in the net
  def transition_range(self):
    s = self._solver
    tvs = self._transition_vars
    
    def rng(i, v): # FIXME
      reach = [t["id"] for t in self._net._transitions] # reachable(i)
      return s.lor([s.eq(v, s.num(tid)) for tid in reach])

    rng_constr = [rng(i, v) for (i, v) in enumerate(tvs)]
    return s.land(rng_constr) # + tau_constr)

  # encode data constraints for transition t and instant i
  def data_constraints(self):
    s = self._solver
    dvars = self._data_vars
    svars = self._data_store_vars

    def data_constr(t, i):
      vs = [ v for (v, _) in self._net.get_data_variables()]
      sub = dict(list(dvars[i].items()))
      has_constr = "constraint" in t
      # encode guard constraint
      trans_constr = t["constraint"].toSMT(s,sub) if has_constr else s.true()

      # connection to values stored in tokens
      store_constr = []
      # FIXME combine both cases
      for p in self._net.pre(t):
        pid = p["id"]
        for tok in self._tokens_by_color[p["color"]]:
          is_consumed = self.is_consumed_token(p, t, tok, i)
          # if the token has data, its consumption sets data variables
          if self._net.place_holds_data(p):
            inscription = self._net.get_inscription(pid, t["id"])
            params = [ n for (n, _) in inscription ]
            transfer_vals = s.top()
            keep_vals = s.top()
            # for all data members in inscription, get stored values
            data_insc = [ n for (n, t) in inscription \
              if t in self._net._data_types]
            for (k, vname) in enumerate(data_insc):
              if not vtype in self._net._data_types:
                continue
              eq_trans = s.eq(dvars[i][vname], svars[i][pid][tok][k])
              transfer_vals = s.land([transfer_vals, eq_trans])
              eq_keep = s.eq(svars[i][pid][tok][k], svars[i+1][pid][tok][k])
              keep_vals = s.land([keep_vals, eq_keep])
            store_constr.append(s.implies(is_consumed, transfer_vals))
            store_constr.append(s.implies(s.neg(is_consumed), keep_vals))
      if i <= self._step_bound:
        for p in self._net.post(t):
          pid = p["id"]
          for tok in self._tokens_by_color[p["color"]]:
            is_produced = self.is_produced_token(p, t, tok, i)
            # if the token has data, its production sets data variables
            if self._net.place_holds_data(p):
              inscription = self._net.get_inscription(t["id"], pid)
              params = [ n for (n, _) in inscription ]
              transfer_vals = []
              # for all data members in inscription, get stored values
              data_insc = [ n for (n, t) in inscription \
                if t in self._net._data_types]
              for (k, vname) in enumerate(data_insc):
                print(i, vname, pid, tok, k)
                print(dvars[i])
                print(svars[i+1][pid][tok])
                eq = s.eq(dvars[i][vname], svars[i+1][pid][tok][k])
                transfer_vals.append(eq)
              store_constr.append(s.implies(is_consumed, s.land(transfer_vals)))


      return s.land([trans_constr] + store_constr)

    constr = [ data_constr(t, i) for i in range(0, self._step_bound) \
      for t in self._net._transitions ]
    return s.land(constr)

  def cache_constraints(self):
    s = self._solver
    cnstr = [ s.iff(v,e) for (v,e) in self._consumed_token_cache.values() ]
    cnstr += [ s.iff(v,e) for (v,e) in self._produced_token_cache.values() ]
    # debugging
    debug = []
    return s.land(cnstr + debug)

  def create_marking_variables(self):
    tokens = self._tokens_by_color
    self._marking_vars = []
    for i in range(0, self._step_bound + 1):
      mvarsi = {}
      for p in self._net._places:
        mvarsp = {}
        for token in tokens[p["color"]]:
          name = "M%d_%d_%s" % (i, p["id"], str(token))
          mvarsp[token] = self._solver.boolvar(name)
        mvarsi[p["id"]] = mvarsp
      self._marking_vars.append(mvarsi)

  def create_transition_variables(self):
    name = lambda i: "T" + str(i)
    vs = [ self._solver.intvar(name(i)) for i in range(0, self._step_bound) ]
    self._transition_vars = vs

  def create_object_variables(self):
    max_objs_per_trans = self._max_objs_per_trans
    name = lambda i,k: "O" + str(i) + "_" + str(k)
    vs = [[self._solver.intvar(name(j,k)) for k in range(0,max_objs_per_trans)]\
      for j in range(0, self._step_bound) ]
    self._object_vars = vs
  
  def create_distance_variables(self):
    s = self._solver
    def var(i, j):
      return s.intvar("D" + str(i) + "_" + str(j)) if i >0 or j>0 else s.real(0)
    trace_len = len(self._trace)
    self._distance_vars = [[var(i,j) \
      for j in range(0, trace_len + 1)] for i in range(0, self._step_bound + 1)]

  def create_data_variables(self):
    def create_var(name, vtype):
      type = VarType.from_java(vtype)
      return self._solver.realvar(name) if type == VarType.real else \
        self._solver.intvar(name)

    # data variables for each transition index, like for DPNs
    vs = self._net.get_data_variables()
    self._data_vars = []
    for i in range(0, self._step_bound):
      xis = dict([ (v,create_var("_%s_%i" % (v,i), vtype)) for (v,vtype) in vs])
      self._data_vars.append(xis)

    # variables that store for each place and each possible token for this place
    # and each data member in the token (provided that such members exist) 
    # its value for each instant
    self._data_store_vars = []
    for i in range(0, self._step_bound + 1):
      store_vars_i = {}
      for p in self._net._places:
        store_vars_i[p["id"]] = {}
        if not self._net.place_holds_data(p):
          continue
        for tok in self._tokens_by_color[p["color"]]:
          dvs = []
          for (idx, typ) in enumerate(p["color"]):
            if typ in self._net._data_types:
              name = "_store_%d_%d_%s_%d" % (i, p["id"], str(tok), idx)
              dvs.append(create_var(name, typ))
          store_vars_i[p["id"]][tok] = dvs
      self._data_store_vars.append(store_vars_i)
    print(self._data_store_vars)


  def move_vars(self, trace_len):
    s = self._solver
    var = lambda i, j: s.intvar("move" + str(i) + "_" + str(j))
    return [[var(i,j) \
      for j in range(0, trace_len+1)] for i in range(0, self._step_bound+1)]

  def move_varsx(self, trace_len, k, pre):
    return [[self._solver.eq(self._vs_move[i][j], self._solver.num(k)) \
      for j in range(0, trace_len+1)] for i in range(0, self._step_bound+1)]

  def create_variables(self):
    self.create_marking_variables()
    self.create_transition_variables()
    self.create_object_variables()
    self.create_distance_variables()
    if self._net.has_data():
      self.create_data_variables()
    self._vs_move = self.move_vars(len(self._trace))
    self._vs_log_move = self.move_varsx(len(self._trace), 2, "l")
    self._vs_mod_move = self.move_varsx(len(self._trace), 1, "m")
    self._vs_sync_move = self.move_varsx(len(self._trace), 0, "s")
    self._run_length_var = self._solver.intvar("run_length")
  
  def edit_distance(self):
    dist = self._distance_vars
    vs_log = self._vs_log_move
    vs_mod = self._vs_mod_move
    vs_sync = self._vs_sync_move
    n = self._step_bound
    trace, m = self._trace, len(self._trace)
    s = self._solver
    zero, one = s.num(0), s.num(1)
    vs_trans = self._transition_vars
    #trans_dict = dict([(t["id"], t) for t in dpn.transitions()])
    max_objs_per_trans = self._max_objs_per_trans
    constr = []

    def is_silent(i): # transition i is silent
      return s.lor([ s.eq(vs_trans[i], s.num(t["id"])) \
        for t in self._net.reachable(i) if t["invisible"] ])
    
    silents2 = [ is_silent(i) for i in range(0,n) ]
    self._silents = [s.boolvar("silent"+str(i)) for i in range(0,n) ]
    constr += [ s.iff(v,e) for (v,e) in zip(self._silents, silents2)]

    # force silent nu transitions to occur in beginning
    def is_nu(i): # transition i has outgoing nu inscription
      has_nu = lambda tid: any("nu" in a["inscription"] \
        for a in self._net._arcs if a["source"] == tid)
      return s.lor([ s.eq(vs_trans[i], s.num(t["id"])) \
        for t in self._net.reachable(i) if has_nu(t["id"]) and t["invisible"]])
    nu_count = len(self._net.objects_created_by_silent_transitions())
    nus2 = [ is_nu(i) for i in range(0, nu_count) ]
    nuvars = [s.boolvar("is_nu"+str(i)) for i in range(0,nu_count) ]
    constr += [ s.iff(v,e) for (v,e) in zip(nuvars, nus2)]
    constr += [ s.implies(nuvars[i], nuvars[i-1]) for i in range(1, nu_count) ]
    
    # cost for model step: number of objects used
    num_objs_used = lambda i: reduce(lambda acc, v: \
      s.plus(acc,s.ite(s.eq(v,s.num(-1)),zero,one)), self._object_vars[i], zero) 
    modcost = lambda i: s.ite(self._silents[i], zero, num_objs_used(i))
    modcosts = [s.intvar("mcosti"+str(i)) for i in range(0,n) ]
    constr += [ s.eq(v, modcost(i)) for (i,v) in enumerate(modcosts) ]

    logcost = lambda j: len(trace[j].get_objects())
    logcostup2 = lambda j: sum([len(trace[j].get_objects()) \
      for k in range(0,j+1)])

    def no_object_diff(i,j): # i is position in transition sequence, j in trace 
      # FIXME independent from i
      trace_objs = [s.num(self._ids_by_object_name[o]) \
        for o in trace[j].get_objects()]
      used = lambda id: s.lor([s.eq(v,id) for v in self._object_vars[i]])
      allused = s.land([ used(oid) for oid in trace_objs ])
      return s.land([s.eq(num_objs_used(i), s.num(len(trace_objs))), allused])

    no_odiff_vars = [ [ s.boolvar("noobjdiff%d_%d" % (i,j)) \
        for j in range(0,m)] for i in range(0,n) ]
    constr += [ s.iff(no_odiff_vars[i][j], no_object_diff(i,j)) \
      for j in range(0,m) for i in range(0,n)]
    
    def sync_step(i, j):
      return [ s.land([s.eq(vs_trans[i], s.num(t["id"])),no_odiff_vars[i][j]]) \
        for t in self._net.reachable(i) \
        if "label" in t and t["label"] == trace[j].get_activity() ]

    # dist[i][j] represents the edit distance of transition sequence up to
    # including i, and the log up to including j
    # optimization: constraints of form dist[i+1][j+1] = e are equivalent to
    # dist[i+1][j+1] >= e due to minimization. replaced some for performance
    
    # 1. all intermediate distances dist[i][j] are non-negative
    non_neg =[s.ge(dist[i][j],zero) for i in range(0,n+1) for j in range(0,m+1)]
    # 2. if the ith transition is not silent, dist[i+1][0] = dist[i][0] + ocost
    #    where wcost is the writing cost of the ith transition in the model
    base_model = [ s.ge(dist[i+1][0], s.plus(dist[i][0], modcosts[i])) \
      for i in range(0,n)]
    base_model += [ vs_mod[i+1][0] for i in range(0,n)]
    # 3. dist[0][j+1] = (j + 1)
    base_log = [ s.ge(dist[0][j+1], s.num(logcostup2(j))) for j in range(0, m) ]
    base_log += [ vs_log[0][j+1] for j in range(0,m)]
    # 4. if the ith step in the model and the jth step in the log have the
    #    the same label,  dist[i+1][j+1] >= dist[i][j] + penalty, where
    #    penalty accounts for the data mismatch (possibly 0)
    sync_constr = [ s.implies(is_t, s.ge(dist[i+1][j+1], dist[i][j])) \
      for i in range(0,n) for j in range(0,m) \
      for is_t in sync_step(i, j)]
    sync_constr += [ s.implies(vs_sync[i+1][j+1], \
      s.lor([ is_t for is_t in sync_step(i, j)])) \
        for i in range(0,n) for j in range(0,m) ]

    # 5. the ith step in the model and the jth step in the log have different 
    #    labels: dist[i+1][j+1] is minimum of dist[i][j+1], dist[i+1][j]
    #    plus respective penalty values
    for i in range(0,n):
      for j in range(0,m):
        # side constraints on log step (vertical move in matrix)
        log_step = s.implies(vs_log[i+1][j+1], \
          s.ge(dist[i+1][j+1], s.plus(dist[i+1][j], s.num(logcost(j)))))
        constr.append(log_step)
        # side constraints on model step (horizontal move in matrix)
        mod_step = s.implies(vs_mod[i+1][j+1], \
          s.ge(dist[i+1][j+1], s.plus(dist[i][j+1], modcosts[i])))
        constr.append(mod_step)
        v_move = self._vs_move[i+1][j+1]
        constr.append(s.land([s.ge(v_move, zero), s.le(v_move, s.num(2))]))

    # symmetry breaking: enforce log steps before model steps
    # do not enforce at border: would be unsound
    for i in range(2,n-1):
      for j in range(3,m-1):
        c = s.implies(vs_mod[i][j-1], s.neg(vs_log[i][j]))
        constr.append(c)

    constraints = non_neg + base_model + base_log + sync_constr + constr
    return (dist[n][m], s.land(constraints))


  def decode_marking(self, model, j):
    mvars = self._marking_vars[j]
    mstr = ""
    for p in self._net._places:
      pstr = ""
      for t in self._tokens_by_color[p["color"]]:
        if model.eval_bool(mvars[p["id"]][t]):
         pstr += (", " if len(pstr) > 0 else "") + str(t)
        if self._net.place_holds_data(p):
          vars = self._data_store_vars[j][p["id"]][t]
          dtypes = [t for t in p["color"] if t in self._net._data_types ]
          for (tp, var) in zip(dtypes, vars):
            val = model.eval_int(var) if tp=="Integer" else model.eval_real(var)
            pstr += "," + str(val) # FIXME order of objects/data not correct
      mstr += ("%d: [%s] " % (p["id"], pstr))
    return ("MARKING %d: %s\n" % (j, mstr))

  def print_distance_matrix(self, model):
    vs_dist = self._distance_vars
    print("\nDISTANCES:")
    for j in range(0, len(vs_dist[0])):
      d = ""
      for i in range(0, len(vs_dist)):
        s = str(model.eval_int(vs_dist[i][j]))
        d = d + " " + (s if len(s) == 2 else (" "+s))
      print(d)
    vs_move = self._vs_move
    print("\nMOVE TYPES:")
    for j in range(0, len(vs_move[0])):
      d = ""
      for i in range(0, len(vs_move)):
        val = model.eval_int(vs_move[i][j])
        if val == 0:
          assert(model.eval_bool(self._vs_sync_move[i][j]))
        s = str(val)
        d = d + " " + (s if len(s) == 2 else (" "+s))
      print(d)

  def decode_alignment(self, model, run_length):
    vs_sync = self._vs_sync_move
    vs_mod = self._vs_mod_move

    self.print_distance_matrix(model)

    step_type = lambda i, j: "model" if model.eval_bool(vs_mod[i][j]) else "sync" if model.eval_bool(vs_sync[i][j]) else "log"

    i = run_length # self._step_bound # n
    j = len(self._trace) # m
    alignment = [] # array mapping instant to one of {"log", "model","sync"}
    while i >= 0 and j >= 0 and (i > 0 or j > 0):
      cost_current = model.eval_int(self._distance_vars[i][j])
      step = step_type(i,j)
      if step == "model":
        i -= 1
      elif step == "log":
        j -= 1
      else:
        i -= 1
        j -= 1
      cost_step = cost_current - model.eval_int(self._distance_vars[i][j])
      alignment.append((step, cost_step))
    alignment.reverse()
    return alignment

  def decode_alignment_cost(self, model):
    run_length = model.eval_int(self._run_length_var)
    cost_var =  self._distance_vars[run_length][len(self._distance_vars[0])-1]
    return model.eval_int(cost_var)

  def decode(self, model):
    s = self._solver
    tvars = self._transition_vars
    ovars = self._object_vars
    max_objs_per_trans = self._max_objs_per_trans
    out = "DECODE\n"
    run_length = model.eval_int(self._run_length_var)
    out += ("run length %d (bound %d)\n" % (run_length, self._step_bound))
    out += self.decode_marking(model, 0)
    for j in range(0, run_length):
      val = model.eval_int(tvars[j])
      trans = next(t for t in self._net._transitions if t["id"] == val)
      objs = [(model.eval_int(ovars[j][k]), ovars[j][k]) \
        for k in range(0, max_objs_per_trans)]
      objns = [(self._object_name_by_id[id]) \
        for (id, v) in objs if id in self._object_name_by_id]
      out += " " + trans["label"] + str(objns) + "\n"
      out += self.decode_marking(model, j+1)
    
    alignment = self.decode_alignment(model, run_length)
    out += str(alignment) + "\n"
    return out
