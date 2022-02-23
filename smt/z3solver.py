import time

from z3 import *

from smt.solver import Solver, Model

class Z3Solver(Solver):

  def __init__(self):
    self.ctx = Optimize()

  def are_equal_expr(self, a, b):
    return hash(a) == hash(b)
  
  def true(self):
    return And([])
  
  # integer constants
  def num(self, n):
    return n
  
  # real constants
  def real(self, n):
    return n
  
  # boolean variable with name
  def boolvar(self, n):
    return Bool(n)
  
  # integer variable with name
  def intvar(self, n):
    return Int(n)
  
  # real variable with name
  def realvar(self, n):
    return Real(n)
  
  # logical conjunction
  def land(self, l):
    return And(l)

  # logical disjunction
  def lor(self, l):
    return Or(l)

  # logical negation
  def neg(self, a):
    return Not(a)

  # logical implication
  def implies(self, a, b):
    return Implies(a, b)

  # logical biimplication
  def iff(self, a, b):
    return Not(Xor(a, b))

  # equality of arithmetic terms
  def eq(self, a, b):
    return a == b

  # less-than on arithmetic terms
  def lt(self, a, b):
    return a < b

  # greater-or-equal on arithmetic terms
  def ge(self, a, b):
    return a >= b

  # increment arithmetic term by 1
  def inc(self, a):
    return a + 1
  
  # subtraction
  def minus(self, a, b):
    return a - b

  # addition
  def plus(self, a, b):
    return a + b

  # if-then-else
  def ite(self, cond, a, b):
    return If(cond, a, b)

  # minimum of two arithmetic expressions
  def min(self, a, b):
    return self.ite(self.lt(a, b), a, b)
  
  def simplify(self, e):
    return simplify(e)

  def push(self):
    self.ctx.push()

  def pop(self):
    self.ctx.pop()

  # add list of assertions
  def require(self, formulas):
    self.ctx.add(formulas)

  # minimize given expression
  def minimize(self, expr, max_val):
    #print(self.ctx.statistics())
    val = self.ctx.minimize(expr)
    t_start = time.perf_counter()
    result = self.ctx.check()
    self.t_solve = time.perf_counter() - t_start
    return Z3Model(self.ctx) if result == z3.sat else None

  # reset context
  def reset(self):
    self.ctx = Optimize() # Optimize solver does not have reset function
    self.t_solve = 0

  # destroy context and config
  def destroy(self):
    pass

  @staticmethod
  def shutdown():
    pass


class Z3Model(Model):

  def __init__(self, ctx):
    self.model = ctx.model()
  
  def eval_bool(self, v):
    val = self.model.eval(v)
    return bool(val)
  
  def eval_int(self, v):
    if isinstance(v, int):
      return v
    return self.model.eval(v).as_long()
  
  def eval_real(self, v):
    return float(self.model.eval(v).as_fraction())
  