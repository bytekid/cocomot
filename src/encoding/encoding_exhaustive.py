from functools import reduce
from itertools import groupby

from dpn.expr import Expr
from encoding.encoding import Encoding

class ExhaustiveEncoding(Encoding):

  def __init__(self, dpn, solver, step_bound):
    super().__init__(dpn, solver, step_bound)

  def prepare_edit_distance(self, len_trace):
    self._vs_dist = self.edit_distance_vars(len_trace)
    # create move vars
    s = self._solver
    var = lambda i, j: s.intvar("move" + str(i) + "_" + str(j))
    self._vs_moves = [[var(i,j) \
      for j in range(0, len_trace + 1)] for i in range(0, self._step_bound+1)]

  def edit_distance_parametric(self, trace, mcost, syncost):
    delta = self._vs_dist
    vs_moves = self._vs_moves
    n = self._step_bound
    m = len(trace)
    s = self._solver
    dpn = self._dpn
    etrans = [(t["id"], t) for t in dpn.transitions()]

    def is_silent(i): # transition i is silent
      return s.lor([ s.eq(self._vs_trans[i], s.num(id)) \
        for (id, t) in etrans if t in dpn.reachable(i) and t["invisible"] ])
    
    is_silents = [ is_silent(i) for i in range(0,n) ]
    self._silents = [s.boolvar("silent"+str(i)) for i in range(0,n) ]
    silent = [ s.iff(v,e) for (v,e) in zip(self._silents, is_silents)]
    mcostmod = lambda i: s.ite(self._silents[i], s.num(0), mcost(i))

    # constants for move types
    smove = lambda i, j: s.eq(vs_moves[i][j], s.num(0))
    lmove = lambda i, j: s.eq(vs_moves[i][j], s.num(1))
    mmove = lambda i, j: s.eq(vs_moves[i][j], s.num(2))
    
    # 0. move var range
    # first index is column, second is row
    moves = [s.land([s.ge(vs_moves[i][j], s.num(0)), s.ge(s.num(2), vs_moves[i][j])])\
      for i in range(0,n+1) for j in range(0,m+1)]
    # 1. all intermediate distances delta[i][j] are non-negative
    non_neg = [s.ge(delta[i][j], s.num(0))\
      for i in range(0,n+1) for j in range(0,m+1)]
    # 2. if the ith transition is not silent, delta[i+1][0] = delta[i][0] + P_M
    model0 = [ mmove(i+1, 0) for i in range(0,n) ]
    # 3. border moves are log moves
    log0 = [ lmove(0, j+1) for j in range(0,m) ]
    # 4. define move types
    modelmoves = [s.iff(mmove(i+1,j), s.eq(delta[i+1][j], s.plus(mcostmod(i), delta[i][j])))\
      for i in range(0,n) for j in range(0,m+1)]
    logmoves = [s.iff(lmove(i,j+1), s.eq(delta[i][j+1], s.plus(s.num(1), delta[i][j])))\
      for i in range(0,n+1) for j in range(0,m)]
    syncmoves = [s.iff(smove(i+1,j+1), s.eq(delta[i+1][j+1], s.plus(syncost(i, j), delta[i][j])))\
      for i in range(0,n) for j in range(0,m)]
    
    # run length, only relevant for multiple tokens
    length = [s.ge(self._run_length, s.num(0)),s.ge(s.num(n), self._run_length)]
    
    if self._dpn.has_final_places():
      min_expr = delta[n][m]
    else:
      min_expr = delta[0][m]
      for i in range(1,n+1):
        min_expr = s.ite(s.eq(self._run_length, s.num(i)), delta[i][m],min_expr)

    test = [ lmove(0,1), mmove(1,1)]

    constraints = moves + non_neg + model0 + log0 + modelmoves + logmoves + \
      syncmoves + length + silent + test
    return (min_expr, s.land(constraints))
  
  def write_diff_fixed(self, i, j, t):
    s = self._solver
    diff = s.num(0)
    for x in t["write"]:
      if x not in trace[j]["valuation"]:
        diff = s.inc(diff) 
      else:
        val = Expr.numval(trace[j]["valuation"][x])
        diff = s.ite(s.eq(subst_prime[x], s.real(val)), diff, s.inc(diff))
    return diff

  def sync_costs_fixed(self, trace, i, j):
    subst_prime = dict([ (x, v) for (x, v) in self._vs_data[i+1].items() ])
    s = self._solver

    ps = []
    zero = s.real(0)
    for t in self._dpn.reachable(i):
      wdiff = self.write_diff_fixed(i, j, t)
      is_t = s.eq(self._vs_trans[i], s.num(t["id"]))
      if "label" in t and t["label"] == trace[j]["label"]:
        ps.append((is_t, wdiff))
    return ps


  def edit_distance(self, trace):
    s = self._solver
    MAX = 100

    def mcost(i):
      e = s.real(MAX)
      for t in self._dpn.reachable(i):
        e = s.ite(s.eq(self._vs_trans[i], s.num(t["id"])), s.num(len(t["write"]) + 1), e)
      return e
    
    def syncost(i,j):
      e = s.real(MAX)
      for (is_t, penalty) in self.sync_costs_fixed(trace, i, j):
        e = s.ite(is_t, penalty, e)
      return e
  
    return self.edit_distance_parametric(trace, mcost, syncost)


  def negate(self, trace, alignment, model):
    print("\nMOVES:")
    for j in range(0, len(self._vs_moves[0])):
      d = ""
      for i in range(0, len(self._vs_moves)):
        d = d + " " + str(model.eval_int(self._vs_moves[i][j]))
      print(d)

    transs = dict([ (t["id"], t) for t in self._dpn.transitions() ])
    s = self._solver
    length = len(alignment["run"]["transitions"])
    # length should coincide with decoded run_length
    vs_moves = self._vs_moves
    sol = [s.eq(s.num(length), self._run_length)]
    j = len(trace)
    i = length
    while i > 0 or j > 0:
      move = model.eval_int(vs_moves[i][j])
      sol.append(s.eq(vs_moves[i][j], s.num(move)))
      i -= 0 if move == 1 else 1
      j -= 0 if move == 2 else 1

    for (i,(tid, tlabel)) in enumerate(alignment["run"]["transitions"]):
      sol.append(s.eq(self._vs_trans[i], s.num(tid)))
    print([str(s) for s in sol])
    return s.neg(s.land(sol))


  def decode_alignment(self, trace, model):
    m = len(trace)
    vs_dist = self._vs_dist
    transs = dict([ (t["id"], t) for t in self._dpn.transitions() ])
    run_length_dec = self.decode_run_length(model)
    distance = model.eval_int(vs_dist[run_length_dec][len(trace)])
    run = self.decode_process_run(model, run_length_dec)
    (markings, transitions, valuations) = run
    run_length = len(transitions)
    self.print_distance_matrix(model)

    i = run_length # self._step_bound # n
    j = len(trace) # m
    alignment = [] # array mapping instant to one of {"log", "model","parallel"}
    moves = ""
    while i > 0 or j > 0:
      move = model.eval_int(self._vs_moves[i][j])
      moves += "S " if move == 0 else "L " if move == 1 else "M "
      if move == 2:
        if not self._dpn.is_silent_final_transition(transitions[i-1][0]):
          alignment.append("model")
        i -= 1
      elif move == 1:
        alignment.append("log")
        j -= 1
      else:
        alignment.append("parallel")
        i -= 1
        j -= 1
    
    alignment.reverse()
    print(moves[::-1])
    return {
      "run": {
        "transitions": transitions,
        "markings":    markings, 
        "valuations":  valuations
      },
      "alignment":   alignment,
      "cost":        distance
    }
  