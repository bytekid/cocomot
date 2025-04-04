import time

from z3 import *

from smt.solver import Solver, Model

class Z3Solver(Solver):

  def __init__(self, incremental=False):
    self._incremental = incremental
    self.t_solve = 0
    if not incremental:
      self.ctx = Optimize()
      self.ctx.set('optsmt_engine', 'symba') # no weird timeouts on simple traces 
    else:
      self.ctx = z3.Solver()
    set_param('model.completion', True)
    self.ctx.set("timeout", 600000) # timeout in milliseconds
    self.cnt = 0
    self.t_solve = 0

  def to_string(self, e):
    return str(e)

  def are_equal_expr(self, a, b):
    return hash(a) == hash(b)
  
  def true(self):
    return True
  
  def false(self):
    return False
  
  # integer constants
  def num(self, n):
    return IntVal(n)
  
  # real constants
  def real(self, n):
    return RealVal(n)
  
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
    return And(l) if len(l) > 0 else self.true()

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

  # less-than-or-equal on arithmetic terms
  def le(self, a, b):
    return a <= b

  # greater-than on arithmetic terms
  def gt(self, a, b):
    return a > b

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

  # multiplication
  def mult(self, a, b):
    return a * b

  # if-then-else
  def ite(self, cond, a, b):
    return If(cond, a, b)

  # absolute value
  def abs(self, x):
    return If(x > 0, x, - x)

  def get_bool_sort(self):
    return BoolSort()

  def get_int_sort(self):
    return IntSort()

  def get_real_sort(self):
    return RealSort()

  def mk_fun(self, name, isorts, osort):
    sorts = isorts + [osort]
    return Function(name, *sorts)

  def apply_fun(self, f, args):
    return f(*args)

  def distinct(self, xs):
    return Distinct(xs)
  
  def simplify(self, e):
    return simplify(e)

  def push(self):
    if self.ctx.check() == sat:
      self.ctx.push()
    else:
      print (self.ctx.unsat_core())

  def pop(self):
    self.ctx.pop()

  # add list of assertions
  def require(self, formulas):
    self.ctx.add(formulas)
    #for f in formulas:
    #  c = Bool("b" + str(self.cnt))
    #  self.cnt += 1
    #  print(c, "=", f)
    #  self.ctx.assert_and_track(f, c)

  def is_sat(self):
    return self.ctx.check() == z3.sat

  def check_sat(self, constr):
    self.push()
    self.require(constr)
    m = Z3Model(self.ctx) if self.ctx.check() == z3.sat else None
    self.pop()
    return m

  # maximize given expression
  def maximize(self, expr, bound_val):
    val = self.ctx.maximize(expr)
    t_start = time.perf_counter()
    result = self.ctx.check()
    self.t_solve = time.perf_counter() - t_start
    return Z3Model(self.ctx) if result == z3.sat else None


  # minimize given expression
  def minimize(self, e, max):
    return self.minimize_inc(e, max) if self._incremental \
      else self.minimize_builtin(e, max)

  # minimize given expression
  def minimize_builtin(self, expr, max_val):
    self.push()
    self.require([self.le(expr, max_val)])
    val = self.ctx.minimize(expr)
    t_start = time.perf_counter()
    result = self.ctx.check()
    self.t_solve = time.perf_counter() - t_start
    m = Z3Model(self.ctx) if result == z3.sat else None
    if not m:
      self.pop()
    return m

  def minimize_inc(self, expr, max_val, start = 0):
    self.push()
    val = start
    self.require(self.land([self.eq(expr, self.num(val))]))
    t_start = time.perf_counter()
    status = self.ctx.check()
    if status == z3.unknown:
      return None
    m = Z3Model(self.ctx) if status == z3.sat else None
    self.pop()
    self.t_solve = time.perf_counter() - t_start
    while status != z3.sat and val <= max_val:
      self.push()
      val += 1
      self.require(self.land([self.eq(expr, self.num(val))]))
      t_start = time.perf_counter()
      status = self.ctx.check()
      if status == z3.unknown:
        return None
      m = Z3Model(self.ctx) if status == z3.sat else None
      self.pop()
      self.t_solve += time.perf_counter() - t_start
    return None if val > max_val else m

  def check(self):
    t_start = time.perf_counter()
    status = self.ctx.check()
    self.t_solve = time.perf_counter() - t_start
    return Z3Model(self.ctx) if status == z3.sat else None

  # reset context
  def reset(self):
    if self._incremental:
      self.ctx.reset()
    self.t_solve = 0

  # destroy context and config
  def destroy(self):
    del self.ctx

  @staticmethod
  def shutdown():
    pass


class Z3Model(Model):

  def __init__(self, ctx):
    self.ctx = ctx
    self.model = ctx.model()
  
  def eval_bool(self, v):
    return bool(self.model.eval(v, model_completion=True))
  
  def eval_int(self, v):
    if isinstance(v, int):
      return v
    return self.model.eval(v, model_completion=True).as_long()
  
  def eval_real(self, v):
    if isinstance(v, float) or isinstance(v, int):
      return float(v)
    val = self.model.eval(v, model_completion=True)
    if isinstance(val, IntNumRef):
      return float(val.as_long())
    return float(val.as_fraction())

  def destroy(self):
    self.ctx.pop()
    del self.model
  