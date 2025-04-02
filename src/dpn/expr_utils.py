from abc import ABCMeta, abstractmethod

from dpn.expr import *

def conjuncts(e):
  if isinstance(e, BinCon) and e.op == "&&":
    return conjuncts(e.left) + conjuncts(e.right)
  return [e]

def constants(e):
  if isinstance(e, Num):
    return set([e.num])
  elif isinstance(e, BinCon) or isinstance(e, BinOp) or isinstance(e, Cmp):
    return constants(e.left).union(constants(e.right))
  elif isinstance(e, UnCon):
    return constants(e.arg)
  return set([])


# visitor
class Visitor:
    STOP_RECURSION = True
    @abstractmethod
    def visit_var(self, element):
        pass

    @abstractmethod
    def visit_num(self, element):
        pass
    
    @abstractmethod
    def visit_propvar(self, element):
        pass

    @abstractmethod
    def visit_bool(self, element):
        pass

    @abstractmethod
    def visit_char(self, element):
        pass

    @abstractmethod
    def visit_pred(self, element):
        pass

    @abstractmethod
    def visit_fun(self, element):
        pass

    @abstractmethod
    def visit_fun(self, element):
        pass

    @abstractmethod
    def visit_binop(self, element):
        pass

    @abstractmethod
    def visit_cmp(self, element):
        pass

    @abstractmethod
    def visit_bincon(self, element):
        pass
  

class VarFlipper(Visitor):
  def __init__(self):
    pass

  def visit_var(self, v):
    v.is_prime = not (v.is_prime)


class VarReplacer(Visitor):
  def __init__(self, subst):
    self._subst = subst

  def visit_var(self, v):
    if v.name in self._subst:
      repl = self._subst[v.name]
      #assert(not(isinstance(repl, list)))
      v.name = repl
  

class ListExpander(Visitor):
  def __init__(self):
    self._change = False

  def visit_fun(self, f):
    unary_fun = lambda t: isinstance(t, Fun) and len(t._args) == 1
    if unary_fun(f) and unary_fun(f._args[0]):
      arg = f._args[0]._args[0]
      if isinstance(arg, Var) and isinstance(arg.name, list):
        xs = arg.name
        fname = f._args[0]._name # function name
        f._args = [ Fun(fname, [ Var(x, None) ]) for x in xs ] # distribute
        self._change = True
        return self.STOP_RECURSION

class ObjectPropertyReplacer(Visitor):
  def __init__(self, objects):
    self._objects = objects

  def replace_arg(self, arg):
    unary_fun = lambda t: isinstance(t, Fun) and len(t._args) == 1
    if unary_fun(arg) and isinstance(arg._args[0], Var):
      ovmap = self._objects[arg._args[0].name]["ovmap"]
      if arg._name in ovmap:
        val = ovmap[arg._name]
        return Num(val)
    return arg

  def visit_fun(self, fun):
    args = [ self.replace_arg(a) for a in fun._args]
    fun._args = args

  def visit_cmp(self, cmp):
    cmp.left = self.replace_arg(cmp.left)
    cmp.right = self.replace_arg(cmp.right)

  def visit_binop(self, cmp):
    cmp.left = self.replace_arg(cmp.left)
    cmp.right = self.replace_arg(cmp.right)
