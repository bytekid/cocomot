class Encoding():
  def __init__(self, solver, net, trace):
    self._solver = solver
    self._net = net
    self._trace = trace
    self._step_bound = net.step_bound(trace)
    #self._object_bound = net.object_bound(trace)
    net.compute_reachable(self._step_bound)
    self._objects_by_type = self._net.objects_by_type(self._trace)
    oids = [ (n, id) for os in self._objects_by_type.values() for (n, id) in os]
    self._ids_by_object_name = dict(oids)
    self._object_name_by_id = dict([(id,n) for (n, id) in oids])
    print("OBJECT IDS", self._object_name_by_id)
    self._tokens_by_color = self._net.tokens_by_color(self._trace)
    # cache encoding parts
    self._consumed_token_cache = {}
    self._produced_token_cache = {}

  def get_solver(self):
    return self._solver

  def get_step_bound(self):
    return self._step_bound

  def initial_state(self):
    s = self._solver
    mvars0 = [v for vs in self._marking_vars[0].values() for v in vs.values()]
    # FIXME fixed to empty marking
    return s.land([s.neg(v) for v in mvars0])

  def final_state(self):
    # FIXME how to specify final marking?
    # currently we only require that places marked as final have some token
    last_marking = self._marking_vars[self._step_bound]
    constraints = []
    for p in self._net._places:
      tokens_in_place = []
      for t in self._tokens_by_color[p["color"]]:
        token_placed = last_marking[p["id"]][t] if "final" in p and p["final"] \
          else self._solver.neg(last_marking[p["id"]][t])
        tokens_in_place.append(token_placed)
      constraints.append(self._solver.lor(tokens_in_place))
    return self._solver.land(constraints)


  def is_fired_token(self, p, t, tok, j, incoming):
    s = self._solver
    ovars = self._object_vars
    # print("\nIS %s TOKEN:" % ("CONSUMED" if incoming else "PRODUCED"), "place", p["id"], t["label"], "instant", j, tok)
    obj_params = self._net.object_inscriptions_of_transition(t, self._trace)
    params = [x for x in obj_params if x["place"] == p["id"] and \
      x["incoming"] == incoming]
    #print(" ", params)
    eqs = []
    inscription = next(a["inscription"] for a in self._net._arcs \
      if (incoming and a["source"] == p["id"] and a["target"] == t["id"]) or \
        (not incoming and a["target"] == p["id"] and a["source"] == t["id"]))
    params_for_insc = []
    for (pname, _) in inscription:
      params_for_insc.append([x for x in params if x["name"] == pname])
    #print(" for insc ", params_for_insc)
    for (obj, params) in zip(tok, params_for_insc):
      objid = self._ids_by_object_name[obj]
      inst2token = [ s.eq(ovars[j][p["index"]], s.num(objid)) for p in params]
      eqs.append(s.lor(inst2token))
    # print(" ", s.land(eqs))
    return s.land(eqs)

  def is_consumed_token(self, p, t, tok, j):
    #return self.is_fired_token(p, t, tok, j, True)

    keytuple = (p["id"], t["id"], tok, j)
    if keytuple in self._consumed_token_cache:
      return self._consumed_token_cache[keytuple][0]
    
    expr = self.is_fired_token(p, t, tok, j, True)
    index = len(self._consumed_token_cache)
    var = self._solver.boolvar("cons_token" + str(index))
    self._consumed_token_cache[keytuple] = (var, expr)
    return var

  def is_produced_token(self, p, t, tok, j):
    #return self.is_fired_token(p, t, tok, j, False)

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
          pid = p["id"]
          marked = s.land([mvars[j][pid][tok], s.neg(mvars[j+1][pid][tok])])
          cnstr.append(s.implies(self.is_consumed_token(p, t, tok, j), marked))
      return s.land(cnstr)

    def trans_j_produced(t, j):
      cnstr = []
      for p in self._net.post(t):
        for tok in self._tokens_by_color[p["color"]]:
          marked = mvars[j+1][p["id"]][tok]
          cnstr.append(s.implies(self.is_produced_token(p, t, tok, j), marked))
      return s.land(cnstr)

    cstr = [s.implies(s.eq(self._transition_vars[j], s.num(t["id"])), \
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
    max_objs = self._net.get_max_objects_per_transition(self._trace)

    def trans_j_constraint(t, j):
      obj_params = self._net.object_params_of_transition(t, self._trace)
      obj_conj = []
      objs_by_type = self._net.objects_by_type(self._trace)
      for param in obj_params:
        pidx = param["index"]
        # kth object parameter of transition t
        param_disj = [ s.eq(ovars[j][pidx], s.num(id)) \
          for (obj_name, id) in objs_by_type[param["type"]]]
        if not param["needed"]:
          param_disj.append(s.eq(ovars[j][pidx], s.num(0)))
        obj_conj.append(s.lor(param_disj))
      for pidx in range(len(obj_params), max_objs): # unused object indices
        obj_conj.append(s.eq(ovars[j][pidx], s.num(-1)))
      return s.land(obj_conj)

    cstr = [s.implies(s.eq(tvars[j], s.num(t["id"])), trans_j_constraint(t,j)) \
      for j in range(0, self._step_bound) \
      for t in self._net._transitions]
    return s.land(cstr)
  

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

    def nutrans_constraint(t, j):
      obj_params = self._net.object_params_of_transition(t, self._trace)
      constraints = []
      for param in obj_params:
        k = param["index"]
        # kth object parameter of transition t
        if not "nu" in param["name"]:
          continue
        # marking j is before transition j
        imps = [s.implies(s.eq(ovars[j][k], s.num(id)), not_in_marking(id,j)) \
          for (obj_name, id) in self._objects_by_type[param["type"]]]
        constraints += imps
      return s.land(constraints)

    cstr = [s.implies(s.eq(tvars[j], s.num(t["id"])), nutrans_constraint(t,j)) \
      for j in range(0, self._step_bound) \
      for t in self._net.nu_transitions() ]
    return s.land(cstr)

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

  def cache_constraints(self):
    s = self._solver
    cnstr = [ s.iff(v,e) for (v,e) in self._consumed_token_cache.values() ]
    cnstr += [ s.iff(v,e) for (v,e) in self._produced_token_cache.values() ]

    # debugging
    debug = []
    mvars = self._marking_vars
    token1 = tuple(["order1"])
    token2 = tuple(["order2"])
    #debug.append(mvars[1][0][token1])
    #debug.append(mvars[2][0][token1])
    # debug.append(mvars[2][0][token2])

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
    max_objs_per_trans = self._net.get_max_objects_per_transition(self._trace)
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

  def create_variables(self):
    self.create_marking_variables()
    self.create_transition_variables()
    self.create_object_variables()
    self.create_distance_variables()


  def edit_distance(self):
    return (self._solver.num(0), self._solver.true())

  def decode_marking(self, model, j):
    mvars = self._marking_vars[j]
    mstr = ""
    for p in self._net._places:
      pstr = ""
      for t in self._tokens_by_color[p["color"]]:
        if model.eval_bool(mvars[p["id"]][t]):
         pstr += (", " if len(pstr) > 0 else "") + str(t)
      mstr += ("%d: [%s] " % (p["id"], pstr))
    print("MARKING %d: %s" % (j, mstr))

  def decode_alignment(self, model):
    s = self._solver
    tvars = self._transition_vars
    ovars = self._object_vars
    max_objs_per_trans = self._net.get_max_objects_per_transition(self._trace)
    print("DECODE")
    self.decode_marking(model, 0)
    for j in range(0, self._step_bound):
      val = model.eval_int(tvars[j])
      trans = next(t for t in self._net._transitions if t["id"] == val)
      objs = [(model.eval_int(ovars[j][k]), ovars[j][k]) for k in range(0, max_objs_per_trans)]
      objs = [(self._object_name_by_id[id]) for (id, v) in objs if id in self._object_name_by_id]
      print(" ", trans["label"], objs)
      
      #place = next(p for p in self._net._places if p["id"] == 0)
      #token1 = tuple(["order1"])
      #token2 = tuple(["order2"])
      #print("prod token1", model.eval_bool(self.is_produced_token(place, trans, token1,j)))
      #print("prod token2", model.eval_bool(self.is_produced_token(place, trans, token2,j)))

      self.decode_marking(model, j+1)
    
    #mvars = self._marking_vars
    #print("mvars[1][0][order1]", model.eval_bool(mvars[1][0][token1]))
    #print("mvars[1][0][order1]", model.eval_bool(mvars[2][0][token1]))
    #print("mvars[1][0][order2]", model.eval_bool(mvars[2][0][token2]))
