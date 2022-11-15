from optimathsat import *
import _optimathsat as om

from fractions import Fraction

class OptiMathsatSolver:
  cfg = None
  env = None

  def __init__(self):
    self.cfg = om.msat_create_config()
    om.msat_set_option(self.cfg, "opt.maxsmt_engine", "maxres")
    om.msat_set_option(self.cfg, "model_generation", "true")
    self.env = om._msat_create_opt_env(self.cfg)
    assert not om.MSAT_ERROR_CONFIG(self.cfg)

  def __del__(self):
    self.destroy()

  def destroy(self):
    om.msat_destroy_config(self.cfg)
    om.msat_destroy_env(self.env)
    del self.cfg
    del self.env
    return

  def are_equal_expr(self, a, b):
    a == b # FIXME correct?
  
  def true(self):
    om.msat_make_true(self.env)
  
  # integer constants
  def num(self, n):
    return om.msat_make_number(self.env, str(n))
  
  # real constants
  def real(self, r):
    frac = Fraction(r)
    rstr = str(frac.numerator) + "/" + str(frac.denominator)
    return om.msat_make_number(self.env, rstr)
  
  # boolean variable with name
  def boolvar(self, name):
    booltype = om.msat_get_bool_type(self.env)
    decl = om.msat_declare_function(self.env, name, booltype)
    return om.msat_make_constant(self.env, decl)
  
  # integer variable with name
  def intvar(self, name):
    inttype = om.msat_get_integer_type(self.env)
    decl = om.msat_declare_function(self.env, name, inttype)
    return om.msat_make_constant(self.env, decl)
  
  # real variable with name
  def realvar(self, name):
    rattype = om.msat_get_rational_type(self.env)
    decl = om.msat_declare_function(self.env, name, rattype)
    return om.msat_make_constant(self.env, decl)
  
  # logical conjunction
  def land(self, args):
    res = om.msat_make_true(self.env)
    for a in args:
      res = om.msat_make_and(self.env, res, a)
    return res 

  # logical disjunction
  def lor(self, args):
    res = om.msat_make_false(self.env)
    for a in args:
      res = om.msat_make_or(self.env, res, a)
    return res 

  # logical negation
  def neg(self, a):
    return om.msat_make_not(self.env, a)

  # logical implication
  def implies(self, a, b):
    return self.lor([self.neg(a), b])

  # logical biimplication
  def iff(self, a, b):
    return self.land([self.implies(a, b), self.implies(b, a)])

  # equality of arithmetic terms
  def eq(self, a, b):
    return om.msat_make_equal(self.env, a, b)

  # less-than on arithmetic terms
  def lt(self, a, b):
    return self.neg(self.ge(a,b))

  # greater-or-equal on arithmetic terms
  def ge(self, a, b):
    return om.msat_make_leq(self.env, b, a)

  # increment of arithmetic term by 1
  def inc(self, a):
    one = om.msat_make_number(self.env, "1")
    return self.plus(a, one)
  
  # subtraction
  def minus(self, a, b):
    n_one = om.msat_make_number(self.env, "-1")
    nb = om.msat_make_times(self.env, n_one, b)
    return om.msat_make_plus(self.env, a, nb)

  # addition
  def plus(self, a, b):
    return om.msat_make_plus(self.env, a, b)

  # if-then-else
  def ite(self, cond, a, b):
    return om.msat_make_term_ite(self.env, cond, a, b)

  def push(self):
    om.msat_push_backtrack_point(self.env)

  def pop(self):
    om.msat_pop_backtrack_point(self.env)

  # add list of assertions
  def require(self, fs):
    res = self.land(fs) if isinstance(fs, list) else fs
    ret = om.msat_assert_formula(self.env, res)
    if ret != 0:
      raise Exception("Unable to assert constraint.")

  # minimize given expression
  def minimize(self, e):
    assert not om.MSAT_ERROR_ENV(self.env)
    obj = om._msat_make_minimize(self.env, e)
    assert not om.MSAT_ERROR_OBJECTIVE(obj)
    ret = om._msat_assert_objective(self.env, obj)
    if ret != 0:
      raise Exception("Unable to assert objective.")
    # ret=0: unsat, ret > 0: sat, ret < 0: unknown
    ret = om.msat_solve(self.env)
    print(ret)
    return Model(om.msat_get_model(self.env)) if ret > 0 else None

  # reset context
  def reset(self):
    om.mset_resetenv(self.env)

  @staticmethod
  def shutdown():
    pass


class Model:

  def __init__(self, mdl):
    self.mdl = mdl
  
  def eval_bool(self, v):
    return om.msat_model_eval(self.mdl, v)
  
  def eval_int(self, v):
    return om.msat_model_eval(self.mdl, v)
  
  def eval_real(self, v):
    return om.msat_model_eval(self.mdl, v)

  def destroy(self):
    om.msat_destroy_model(self.mdl)



if __name__ == "__main__":
  slv = OptiMathsatSolver()
  slv.push()
  slv.pop()
  ten = slv.real(10)
  two = slv.real(2)
  x = slv.realvar("x")
  y = slv.realvar("y")
  slv.require(slv.ge(x, two))
  slv.require(slv.ge(y, two))
  slv.require(slv.lt(ten, slv.plus(x,y)))
  mdl = slv.minimize(y)
  if mdl:
    print(mdl.eval_int(x))