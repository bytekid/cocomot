from abc import ABCMeta, abstractmethod
from functools import reduce

from utils import VarType

class Expr:
  __metaclass__ = ABCMeta

  strmap = {}

  @abstractmethod
  def toSMT(self, solver, subst):
      pass
  
  @abstractmethod
  def vars(self, subst):
      pass

  @staticmethod
  def numval(s):
    try:
      val = float(s)
    except Exception:
      if s.lower() == "true" or s.lower() == "false":
        val = 1 if s.lower() == "true" else 0
      elif isinstance(s,str):
        if s in Expr.strmap:
          val = Expr.strmap[s]
        else:
          val = len(Expr.strmap)
          Expr.strmap[s] = val
    return val

  @staticmethod
  def strval(numval):
    strs = [s for (s,n) in Expr.strmap.items() if n == numval]
    return strs[0] if len(strs) > 0 else "?"



class Term(Expr):
  def __init__(self):
    pass

  def toSMT(self, solver, subst):
    pass

class NotFound(Exception):
  pass

class Var(Term):
  def __init__(self, c, prime, type=VarType.real):
    #assert(isinstance(c, basestring))
    self.name = c
    self.is_prime = (prime != None)
  
  def basename(self):
    return self.name
  
  def __str__(self):
    return str(self.name) + ("'" if self.is_prime else "")

  def toSMT(self, solver, subst):
    return subst[str(self)] if str(self) in subst else solver.realvar(str(self))

  def vars(self): # returns basename without '
    return set([self.name])

  def value(self, subst):
    if str(self) in subst:
      return subst[str(self)]
    else:
      raise NotFound

  def accept(self, visitor):
    visitor.visit_var(self)


class Num(Term):
  def __init__(self, c, t = VarType.real):
    self.type = t
    self.num = c
  
  def __str__(self):
    return self.num

  def toSMT(self, solver, subst):
    return solver.real(self.num)

  def vars(self):
    return set([])

  def value(self, subst):
    return float(self.num)

  def accept(self, visitor):
    visitor.visit_num(self)


class Charstr(Term):

  def __init__(self, c):
    self.chr = c
  
  def __str__(self):
    return '"' + self.chr + '"'

  def toSMT(self, solver, subst):
    return solver.num(Expr.numval(self.chr))

  def vars(self):
    return set([])

  def value(self, subst):
    return Expr.numval(self.chr)

  def accept(self, visitor):
    visitor.visit_char(self)


class Bool(Term):
  strmap = {}

  def __init__(self, c):
    c = c.lower()
    assert(c == "true" or c == "false")
    self.val = (c == "True")
  
  def __str__(self):
    return 'True' if self.val else 'False'

  def toSMT(self, solver, subst):
    return solver.num(1) if self.val else solver.num(0)

  def vars(self):
    return set([])

  def value(self, subst):
    return Expr.numval(self.chr)

  def accept(self, visitor):
    visitor.visit_bool(self)

top = Bool("True")

class BinOp(Term):

  def __init__(self, a, op, b):
    self.op = op
    assert(op == "+" or op == "-")
    self.left = a
    self.right = b
  
  def __str__(self):
    return "(" + str(self.left) + " " + self.op + " " +\
		       str(self.right) + ")"

  def toSMT(self, solver, subst):
    op_funs = {
      "+"  : lambda a, b: solver.plus(a, b),
      "-" : lambda a, b: solver.minus(a, b),
    }
    (l, r) = (self.left.toSMT(solver, subst), self.right.toSMT(solver, subst))
    return op_funs[self.op](l, r)

  def vars(self):
    return self.left.vars().union(self.right.vars())

  def value(self, subst):
    if self.op == "+":
      return self.left.value(subst) + self.right.value(subst)
    else:
      return self.left.value(subst) - self.right.value(subst)

  def accept(self, visitor):
    stop = visitor.visit_binop(self)
    if not (stop == visitor.STOP_RECURSION):
      self.left.accept(visitor)
      self.right.accept(visitor)


class Cmp(Term):

  def __init__(self, op, a, b):
    self.op = op
    assert(op in ["==", ">=", "<=", "<", ">", "!="])
    self.left = a
    self.right = b

  def __str__(self):
    return "(" + str(self.left) + " " + self.op + " " +\
		       str(self.right) + ")"

  def toSMT(self, solver, subst):
    op_funs = {
      "=="  : lambda a, b: solver.eq(a, b),
      ">=" : lambda a, b: solver.ge(a, b),
      "<=" : lambda a, b: solver.ge(b, a),
      ">"  : lambda a, b: solver.lt(b, a),
      "<"  : lambda a, b: solver.lt(a, b),
      "!=" : lambda a, b: solver.neg(solver.eq(a, b)),
    }
    (l, r) = (self.left.toSMT(solver, subst), self.right.toSMT(solver, subst))
    return op_funs[self.op](l, r)

  def vars(self):
    return self.left.vars().union(self.right.vars())
  
  def comparisons(self):
    return set([self])

  def valid(self, subst):
    try:
      if self.op == "==":
        return self.left.value(subst) == self.right.value(subst)
      elif self.op == ">=":
        return self.left.value(subst) >= self.right.value(subst)
      elif self.op == "<=":
        return self.left.value(subst) <= self.right.value(subst)
      elif self.op == ">":
        return self.left.value(subst) > self.right.value(subst)
      elif self.op == "<":
        return self.left.value(subst) < self.right.value(subst)
      else:
        return self.left.value(subst) != self.right.value(subst)
    except NotFound: # variable not found
      return False

  def accept(self, visitor):
    stop = visitor.visit_cmp(self)
    if not (stop == visitor.STOP_RECURSION):
      self.left.accept(visitor)
      self.right.accept(visitor)


class BinCon(Term):

  def __init__(self, a, op, b):
    self.op = op
    assert(op == "&&" or op == "||")
    self.left = a
    self.right = b
  
  def __str__(self):
    return "(" + str(self.left) + " " + self.op + " " +\
		       str(self.right) + ")"

  def toSMT(self, solver, subst):
    op_funs = {
      "&&"  : lambda a, b: solver.land([a, b]),
      "||" : lambda a, b: solver.lor([a, b]),
    }
    (l, r) = (self.left.toSMT(solver, subst), self.right.toSMT(solver, subst))
    return op_funs[self.op](l, r)

  def vars(self):
    return self.left.vars().union(self.right.vars())

  def comparisons(self):
    return self.left.comparisons().union(self.right.comparisons())

  def valid(self, subst):
    try:
      if self.op == "&&":
        return self.left.valid(subst) and self.right.valid(subst)
      else:
        return self.left.valid(subst) or self.right.valid(subst)
    except NotFound: # variable not found
      return False

  def accept(self, visitor):
    stop = visitor.visit_bincon(self)
    if not (stop == visitor.STOP_RECURSION):
      self.left.accept(visitor)
      self.right.accept(visitor)

class Fun(Term):
  def __init__(self, name, args, output_type=None, domain=None):
    self._name = name
    self._args = args
    # FIXME domain might be variadic, and is in any case unknown
    self._domain = domain if domain else VarType.real
    self._type = output_type if output_type else VarType.real
  
  @staticmethod
  def mk_const(name, output_type):
    return Fun(name, [], output_type, [])

  def __eq__(self, obj):
    return isinstance(obj, Fun) and obj._name == self._name and \
      len(obj._args) == len(self._args) and \
      all(obj._args[i] == self._args[i] for i in range(0, len(self._args)))
  
  def __hash__(self):
      return hash((self.__class__.__name__, self._name, len(self._args), \
        tuple([hash(a) for a in self._args])))
  
  def __str__(self):
    argstr = reduce(lambda acc, a: acc + ", " + str(a), self._args, "")
    return self._name + "(" + (argstr[2:] if len(argstr) > 0 else "") + ")"

  def set_type(self, t):
    assert(t == self._type)
  
  def toSMT(self, solver, subst):
    args = [a.toSMT(solver, subst) for a in self._args]
    return solver.mk_fun(self._name, args)

  def vars(self):
    return reduce(lambda acc, a: acc.union(a.vars()), self._args, set([]))

  def comparisons(self):
    return set([ a.comparisons() for a in self._args])

  def basevars(self):
    return reduce(lambda acc, a: acc.union(a.basevars()), self._args, set([]))

  def accept(self, visitor):
    stop = visitor.visit_fun(self)
    if not (stop == visitor.STOP_RECURSION):
      for a in self._args:
        a.accept(visitor)
