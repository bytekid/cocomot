import time
import sys

from pycvc5 import *

from smt.solver import Solver, Model

class CVC5Solver(Solver):

  def __init__(self):
    self._solver = pycvc5.Solver()
    self._solver.setOption("produce-models", "true")
    self._solver.setOption("incremental", "true")
    self._solver.setLogic("LIA")

    self._checks = 0
    self._check_time = 0
    self._simp_time = 0
    self._checked = {}
    self._simped = {}
    self._pop_level = 0
    self._consts = {}


  def destroy(self):
    self.reset() # important: avoid seg fault for multiple checks
    #del self._solver # ... e.g. as in test script

  def are_equal_expr(self, a, b):
    return a == b
  
  def true(self):
    return self._solver.mkTrue()
  
  def false(self):
    return self._solver.mkFalse()
  
  # integer constants
  def num(self, n):
    return self._solver.mkInteger(n)
  
  # real constants
  def real(self, n):
    return self._solver.mkReal(n)
  
  # boolean variable with name
  def boolconst(self, n):
    boolSort = self._solver.getBooleanSort()
    if n in self._consts:
      return self._consts[n]
    else:
      c = self._solver.mkConst(boolSort, n)
      self._consts[n] = c
    return c
  
  # integer variable with name
  def intconst(self, n):
    intSort = self._solver.getIntegerSort()
    return self._solver.mkConst(intSort, n)
  
  # real variable with name
  def realconst(self, n):
    realSort = self._solver.getRealSort()
    return self._solver.mkConst(realSort, n)
  
  # boolean variable with name (might be used for quantification)
  def boolvar(self, n):
    boolSort = self._solver.getBooleanSort()
    return self._solver.mkVar(boolSort, n)
  
  # integer variable with name (might be used for quantification)
  def intvar(self, n):
    intSort = self._solver.getIntegerSort()
    return self._solver.mkVar(intSort, n)
  
  # real variable with name (might be used for quantification)
  def realvar(self, n):
    realSort = self._solver.getRealSort()
    return self._solver.mkVar(realSort, n)
  
  # logical conjunction
  def land(self, l):
    if len(l) == 0:
      return self.true()
    elif len(l) == 1:
      return l[0]
    elif len(l) == 2 and self.is_true(l[0]):
      return l[1]
    return self._solver.mkTerm(kinds.And, *l)

  # logical disjunction
  def lor(self, l):
    if len(l) == 0:
      return self.true().notTerm()
    elif len(l) == 1:
      return l[0]
    return self._solver.mkTerm(kinds.Or, *l)

  # logical negation
  def neg(self, a):
    return self._solver.mkTerm(kinds.Not, a)

  # logical implication
  def implies(self, a, b):
    return self.lor([self.neg(a), b])

  # logical biimplication
  def iff(self, a, b):
    return self.land([self.implies(a,b), self.implies(b, a)])

  # equality of arithmetic terms
  def eq(self, a, b):
    return self._solver.mkTerm(kinds.Equal, a, b)

  def neq(self, a, b):
    return self.neg(self.eq(a,b))
  
  # less-than on arithmetic terms
  def lt(self, a, b):
    return self._solver.mkTerm(kinds.Lt, a, b)

  # greater-or-equal on arithmetic terms
  def ge(self, a, b):
    return self._solver.mkTerm(kinds.Geq, a, b)

  # increment of arithmetic term by 1
  def inc(self, a):
    return self.plus(a, self.num(1))
  
  # subtraction
  def minus(self, a, b):
    return self._solver.mkTerm(kinds.Minus, a, b)

  # addition
  def plus(self, a, b):
    return self._solver.mkTerm(kinds.Plus, a, b)

  # multiplication
  def mult(self, a, b):
    return self._solver.mkTerm(kinds.Mult, a, b)

  # if-then-else
  def ite(self, cond, a, b):
    return self._solver.mkTerm(kinds.Ite, cond, a, b)
  
  # term inspection
  def num_args(self, e):
    return e.getNumChildren()

  def arg(self, e, i):
    return e[i]

  def is_true(self, e):
    return e.isBooleanValue() and e.getBooleanValue()

  def is_false(self, e):
    return e.isBooleanValue() and not e.getBooleanValue()

  def is_int(self, e):
    return e.isIntegerValue()

  def is_real(self, e):
    return e.isRealValue()

  def numeric_value(self, e):
    return e.getIntegerValue() if e.isIntegerValue() else e.getRealValue()

  def is_var(self, e):
    return e.getKind() == kinds.Variable

  def is_not(self, e):
    return e.getKind() == kinds.Not

  def is_and(self, e):
    return e.getKind() == kinds.And

  def is_or(self, e):
    return e.getKind() == kinds.Or

  def is_le(self, e):
    return e.getKind() == kinds.Leq

  def is_lt(self, e):
    return e.getKind() == kinds.Lt

  def is_ge(self, e):
    return e.getKind() == kinds.Geq

  def is_gt(self, e):
    return e.getKind() == kinds.Gt

  def is_eq(self, e):
    return e.getKind() == kinds.Equal

  def is_forall(self, e):
    return e.getKind() == kinds.Forall

  def is_plus(self, e):
    return e.getKind() == kinds.Plus

  def is_minus(self, e):
    return e.getKind() == kinds.Minus

  def is_mult(self, e):
    return e.getKind() == kinds.Mult

  # minimum of two arithmetic expressions
  def min(self, a, b):
    return self.ite(self.lt(a, b), a, b)

  def distinct(self, xs):
    return Terms.distinct(xs)

  def exists(self, xs, e):
    bxs = self._solver.mkTerm(kinds.BoundVarList, xs)
    return self._solver.mkTerm(kinds.Exists, bxs, e)

  def forall(self, xs, e):
    bxs = xs if xs.getKind() == kinds.BoundVarList else \
      self._solver.mkTerm(kinds.BoundVarList, xs) 
    return self._solver.mkTerm(kinds.Forall, bxs, e)

  def subst(self, vars, terms, e):
    for (x, t) in zip(vars, terms):
      e = e.substitute(x, t)
    return e

  def simplify(self, e):
    if e in self._simped:
      return self._simped[e]
    start = time.time()
    ee = self._solver.simplify(e)
    self._simped[e] = ee
    self._simp_time += time.time() - start
    return ee

  def simplify_more(self, e):
    if e in self._simped:
      return self._simped[e]
    start = time.time()
    ee = self._solver.simplify(e)
    self._simped[e] = ee
    self._simp_time += time.time() - start
    return ee

  def qe_simp(self, e):
    if e in self._simped:
      return self._simped[e]
    start = time.time()
    if e.getKind() == kinds.Exists:
      e1 = self._solver.getQuantifierElimination(e)
    else:
      e1 = self._solver.simplify(e)
    self._simped[e] = e1
    self._simp_time += time.time() - start
    return e1

  def push(self):
    try:
      self._solver.push()
      self._pop_level += 1
    except Exception:
      print("constraints unsatisfiable, push() failed")
      exit(1)

  def pop(self):
    assert(self._pop_level > 0)
    self._solver.pop()
    self._pop_level -= 1

  # add list of assertions
  def require(self, formulas):
    self._solver.assertFormula(formulas)

  # check satisfiability
  def check_sat(self, e, eval = None):
    start = time.time()
    if e in self._checked and eval == None:
      return self._checked[e]
    # FIXME hacky: currently dealing with push/pop to keep model long enough
    self.push()
    self._solver.assertFormula(e)
    res = self._solver.checkSat()
    m = CVC5Model(self, eval) if res.isSat() else None
    if eval == None or m == None:
      self._checked[e] = m
      self.pop() # otherwise pop later when destroying model
    self._checks += 1
    self._check_time += time.time() - start
    return m

  # reset context
  def reset(self):
    self._checked = {}
    self._simped = {}
    self._solver.resetAssertions()
  
  def to_string(self, t):
    return str(t)


class CVC5Model(Model):

  def __init__(self, solver, vars):
    self._solver = solver

  def destroy(self):
    self._solver.pop()
  
  def eval_bool(self, v):
    res = self._solver._solver.getValue(v)
    return res.getBooleanValue() if res.isBooleanValue() else False
  
  def eval_int(self, v):
    res = self._solver._solver.getValue(v)
    return res.getIntegerValue() if res.isIntegerValue() else 0
  
  def eval_real(self, v):
    # result of getRealValue is fractions.Fraction
    res = self._solver._solver.getValue(v)
    return float(res.getRealValue()) if res.isRealValue() else 0
