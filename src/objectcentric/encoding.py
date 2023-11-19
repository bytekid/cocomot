class Encoding():
  def __init__(self, solver, net, trace):
    self._solver = solver
    self._net = net
    self._trace = trace
    self._step_bound = net.step_bound(trace)
    self._object_bound = net.object_bound(trace)
    net.compute_reachable(self._step_bound)

  def get_solver(self):
    return self._solver

  def get_step_bound(self):
    return self._step_bound

  def initial_state(self):
    return self._solver.true()

  def final_state(self):
    return self._solver.true()

  def token_game(self):
    return self._solver.true()

  def object_types(self):
    return self._solver.true()

  def freshness(self):
    return self._solver.true()

  def prepare_edit_distance(self):
    pass

  def edit_distance(self):
    return (self._solver.num(0), self._solver.true())

  def decode_alignment(self, trace, model):
    print("decode")