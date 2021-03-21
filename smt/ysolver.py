import time
import sys

from yices import *
from yices import Model as YModel

from smt.solver import Solver, Model

class YicesSolver(Solver):

  def __init__(self):
    sys.stdout.flush()
    self.cfg = Config()
    self.cfg.default_config_for_logic('QF_LRA')
    self.ctx = Context(self.cfg)
    self.t_solve = 0
    self._timeout = 600

  def are_equal_expr(self, a, b):
    return a == b
  
  def true(self):
    return Terms.true()
  
  # integer constants
  def num(self, n):
    return Terms.integer(n)
  
  # real constants
  def real(self, n):
    return Terms.parse_float(str(n))
  
  # boolean variable with name
  def boolvar(self, n):
    bool_t = Types.bool_type()
    return Terms.new_uninterpreted_term(bool_t)
  
  # integer variable with name
  def intvar(self, n):
    int_t = Types.int_type()
    return Terms.new_uninterpreted_term(int_t)
  
  # real variable with name
  def realvar(self, n):
    real_t = Types.real_type()
    return Terms.new_uninterpreted_term(real_t)
  
  # logical conjunction
  def land(self, l):
    return Terms.yand(l)

  # logical disjunction
  def lor(self, l):
    return Terms.yor(l)

  # logical negation
  def neg(self, a):
    return Terms.ynot(a)

  # logical implication
  def implies(self, a, b):
    return Terms.implies(a, b)

  # logical biimplication
  def iff(self, a, b):
    return Terms.iff(a, b)

  # equality of arithmetic terms
  def eq(self, a, b):
    return Terms.arith_eq_atom(a, b)

  # less-than on arithmetic terms
  def lt(self, a, b):
    return Terms.arith_lt_atom(a, b)

  # greater-or-equal on arithmetic terms
  def ge(self, a, b):
    return Terms.arith_geq_atom(a, b)

  # increment of arithmetic term by 1
  def inc(self, a):
    return Terms.add(a, self.num(1))
  
  # subtraction
  def minus(self, a, b):
    return Terms.sub(a, b)

  # addition
  def plus(self, a, b):
    return Terms.add(a, b)

  # if-then-else
  def ite(self, cond, a, b):
    return Terms.ite(cond, a, b)

  # minimum of two arithmetic expressions
  def min(self, a, b):
    return self.ite(self.lt(a, b), a, b)

  def distinct(self, xs):
    return Terms.distinct(xs)

  def push(self):
    try:
      self.ctx.push()
    except Exception:
      print("constraints unsatisfiable, push() failed")
      exit(1)

  def pop(self):
    self.ctx.pop()

  # add list of assertions
  def require(self, formulas):
    self.ctx.assert_formulas(formulas)

  # minimize given expression, with guessed initial value
  def minimize_upordown(self, expr, max_val, start = 0):
    if start == 0:
      return self.minimize(expr, max_val)

    self.push()
    val = start
    self.ctx.assert_formulas([self.ge(self.num(val), expr)])
    t_start = time.perf_counter()
    status = self.ctx.check_context(timeout=self._timeout)
    if status == Status.UNKNOWN:
      return None

    m = YicesModel(self.ctx) if status == Status.SAT else None
    self.pop()
    self.t_solve = time.perf_counter() - t_start
    status0 = status
    (inc, within_bnd) = (-1, lambda v: v > 0) if status == Status.SAT \
      else (1, lambda v: v < max_val) 
    while status == status0 and within_bnd(val):
      self.push()
      val += inc
      print("next %d" % val)
      self.require([self.ge(self.num(val), expr)])
      t_start = time.perf_counter()
      status = self.ctx.check_context(timeout=self._timeout)
      if status == Status.UNKNOWN:
        return None

      mlast = m
      m = YicesModel(self.ctx) if status == Status.SAT else None
      self.pop()
      self.t_solve += time.perf_counter() - t_start
    if inc == -1 and m == None:
      m = mlast
    return m

  # minimize given expression
  def minimize(self, expr, max_val, start = 0):
    self.push()
    val = start
    self.ctx.assert_formulas([self.eq(expr, self.num(val))])
    t_start = time.perf_counter()
    status = self.ctx.check_context(timeout=self._timeout)
    if status == Status.UNKNOWN:
      return None
    m = YicesModel(self.ctx) if status == Status.SAT else None
    self.pop()
    self.t_solve = time.perf_counter() - t_start
    while status != Status.SAT and val <= max_val:
      self.push()
      val += 1
      self.require([self.eq(expr, self.num(val))])
      t_start = time.perf_counter()
      status = self.ctx.check_context(timeout=self._timeout)
      if status == Status.UNKNOWN:
        return None

      m = YicesModel(self.ctx) if status == Status.SAT else None
      self.pop()
      self.t_solve += time.perf_counter() - t_start
    return None if val > max_val else m

  # second version of minimize: use unsatisfiable core (does not seem faster)
  def minimize_core(self, expr, max_val):
    self.push()
    boundsn = [(n,self.ge(self.num(n), expr)) for n in range(0, max_val)]
    bounds = [ e for (n, e) in boundsn ]
    t_start = time.perf_counter()
    status = self.ctx.check_context_with_assumptions(None, bounds)
    m = YicesModel(self.ctx) if status == Status.SAT else None
    core = self.ctx.get_unsat_core() if status != Status.SAT else None
    self.pop()
    self.t_solve = time.perf_counter() - t_start
    cores = []
    while status != Status.SAT and len(bounds) > 0:
      coreexpr = [ e for (n, e) in boundsn if e in core]
      self.require([self.lt(self.num(n), expr) for (n, e) in boundsn if e in core])
      self.push()
      cores = cores + core
      bounds = [ e for (n, e) in boundsn if not e in cores]
      t_start = time.perf_counter()
      status = self.ctx.check_context_with_assumptions(None, bounds)
      m = YicesModel(self.ctx) if status == Status.SAT else None
      core = self.ctx.get_unsat_core() if status != Status.SAT else None
      self.pop()
      self.t_solve += time.perf_counter() - t_start
    return None if bounds == [] else m

  # reset context
  def reset(self):
    self.ctx.reset_context()
    self.status = None
    self.t_solve = 0

  # destroy context and config
  def destroy(self):
    self.cfg.dispose()
    self.ctx.dispose()

  @staticmethod
  def shutdown():
    Yices.exit()
  
  def to_string(self, t):
    return Terms.to_string(t)


class YicesModel(Model):

  def __init__(self, ctx):
    self.model = YModel.from_context(ctx, 1)
  
  def eval_bool(self, v):
    return self.model.get_value(v)
  
  def eval_int(self, v):
    return self.model.get_value(v)
  
  def eval_real(self, v):
    return self.model.get_value(v)
  