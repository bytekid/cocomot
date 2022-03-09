from functools import reduce
from itertools import groupby

from dpn.expr import Expr
from encoding.encoding import *

class UncertaintyEncoding(Encoding):

  def __init__(self, dpn, solver, step_bound):
    super().__init__(dpn, solver, step_bound)

  def prepare_edit_distance(self, trace_len):
    super().prepare_edit_distance(trace_len)
    s = self._solver
    self._vs_drop = [ s.boolvar("drop" + str(j)) for j in range(0, trace_len+1)]

  # return pair of edit distance expression and side constraints
  def edit_distance_parametric(self, trace, lcost, mcost, syncost):
    delta = self._vs_dist
    vs_log = self._vs_log_move
    vs_mod = self._vs_mod_move
    n = self._step_bound
    m = len(trace)
    s = self._solver
    dpn = self._dpn
    vs_trans = self._vs_trans
    vs_data = self._vs_data
    etrans = [(t["id"], t) for t in dpn.transitions()]
    trans_dict = dict(etrans)
    vars = dpn.variables()

    def is_silent(i): # transition i is silent
      return s.lor([ s.eq(vs_trans[i], s.num(id)) \
        for (id, t) in etrans if t in dpn.reachable(i) and t["invisible"] ])
    
    is_silents = [ is_silent(i) for i in range(0,n) ]
    self._silents = [s.boolvar("silent"+str(i)) for i in range(0,n) ]
    silent = [ s.iff(v,e) for (v,e) in zip(self._silents, is_silents)]
    mcostmod = lambda i: s.ite(self._silents[i], s.num(0), mcost(i))

    # delta[i][j] represents the edit distance of transition sequence up to
    # including i, and the log up to including j
    # optimization: constraints of form delta[i+1][j+1] = e are equivalent to
    # delta[i+1][j+1] >= e due to minimization. replaced some for performance

    # 1. all intermediate distances delta[i][j] are non-negative
    non_neg = [s.ge(delta[i][j], s.num(0))\
      for i in range(0,n+1) for j in range(0,m+1)]
    # 2. if the ith transition is not silent, delta[i+1][0] = delta[i][0] + P_M
    model0 = [ s.ge(delta[i+1][0], s.plus(mcostmod(i), delta[i][0])) \
        for i in range(0,n) ]
    # 3. delta[0][j+1] = delta[0][j] + P_L
    log0 = [ s.eq(delta[0][j+1], s.plus(delta[0][j], lcost(j))) \
      for j in range(0,m) ]
    # 4. delta[i+1][j+1] >= delta[i][j] + sync move penalty, where
    #    penalty accounts for the data mismatch (possibly 0)
    #sync = [ s.ge(delta[i+1][j+1], s.plus(syncost(i, j), delta[i][j])) \
    #    for i in range(0,n) for j in range(0,m) ]
    # 5. delta[i+1][j+1] >= delta[i+1][j] + log move penalty
    #log = [ s.ge(delta[i+1][j+1], s.plus(lcost(j), delta[i+1][j])) \
    #    for i in range(0,n) for j in range(0,m) ]
    # 5. delta[i+1][j+1] >= delta[i+1][j] + log move penalty
    #model = [ s.ge(delta[i+1][j+1], s.plus(mcostmod(i), delta[i][j+1])) \
    #    for i in range(0,n) for j in range(0,m) ]
    steps = [ s.lor([s.ge(delta[i+1][j+1], s.plus(syncost(i, j), delta[i][j])),\
                     s.ge(delta[i+1][j+1], s.plus(lcost(j), delta[i+1][j])), \
                     s.ge(delta[i+1][j+1], s.plus(mcostmod(i),delta[i][j+1]))])\
      for i in range(0,n) for j in range(0,m) ]

    # symmetry breaking: enforce log steps before model steps
    #for i in range(2,n):
    #  for j in range(3,m):
    #    c = s.implies(vs_mod[i][j-1], s.neg(vs_log[i][j]))
    #    side_constr.append(c)
    
    # run length, only relevant for multiple tokens
    length = [s.ge(self._run_length, s.num(0)),s.ge(s.num(n), self._run_length)]
    
    if self._dpn.has_final_places():
      min_expr = delta[n][m]
    else:
      min_expr = delta[0][m]
      for i in range(1,n+1):
        min_expr = s.ite(s.eq(self._run_length, s.num(i)), delta[i][m],min_expr)

    constraints = non_neg + model0 + log0 + steps + length + silent
    return (min_expr, s.land(constraints))

  def edit_distance_min(self, trace):
    s = self._solver
    lcost = lambda i: s.num(0 if trace._events[i].is_indeterminate() else 1)
    mcost = lambda _ : s.num(1)
    
    def syncost(i,j):
      #print("syncost", i)
      #print([ (i, t["id"], t["label"]) \
      #  for t in self._dpn.reachable(i) \
      #  if "label" in t and t["label"] in trace._events[j].labels() ])
      is_poss_label = [s.eq(self._vs_trans[i], s.num(t["id"])) \
        for t in self._dpn.reachable(i) \
        if "label" in t and t["label"] in trace._events[j].labels() ]
      return s.ite(s.lor(is_poss_label), s.num(0), s.num(1000))
    
    return self.edit_distance_parametric(trace, lcost, mcost, syncost)