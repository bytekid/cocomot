class Encoding():
  def __init__(self, solver, net, trace):
    self._solver = solver
    self._net = net
    self._trace = trace
    self._step_bound = net.step_bound(trace)
    #self._object_bound = net.object_bound(trace)
    net.compute_reachable(self._step_bound)

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
    return self._solver.true()

  def token_game(self):
    return self._solver.true()

  def object_types(self):
    s = self._solver
    tvars = self._transition_vars
    ovars = self._object_vars

    def trans_j_constraint(t, j):
      obj_params = self._net.object_params_of_transition(t, self._trace)
      obj_conj = []
      objs_by_type = self._net.objects_by_type(self._trace)
      for (k, (param_name, _, needed, ptype)) in enumerate(obj_params):
        # kth object parameter of transition t
        param_disj = [ s.eq(ovars[j][k], s.num(id)) \
          for (obj_name, id) in objs_by_type[ptype]]
        if not needed:
          param_disj.append(s.eq(ovars[j][k], s.num(0)))
        obj_conj.append(s.lor(param_disj))
      return s.land(obj_conj)

    cstr = [s.implies(s.eq(tvars[j], s.num(t["id"])), trans_j_constraint(t,j)) \
      for j in range(0, self._step_bound) \
      for t in self._net._transitions]
    return s.land(cstr)

  def freshness(self):
    return self._solver.true()

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

  def create_marking_variables(self):
    tokens = self._net.tokens_by_color(self._trace)
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
    #print(self._token_vars)

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

  def decode_alignment(self, trace, model):
    print("decode")
