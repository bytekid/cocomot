from abc import ABCMeta, abstractmethod

class Solver:
  __metaclass__ = ABCMeta

  @abstractmethod
  def __init__(self):
    pass

  @abstractmethod
  def are_equal_expr(self, a, b):
    pass
  
  @abstractmethod
  def true(self):
    pass
  
  # integer constants
  @abstractmethod
  def num(self, n):
    pass
  
  # real constants
  @abstractmethod
  def real(self, n):
    pass
  
  # boolean variable with name
  @abstractmethod
  def boolvar(self, n):
    pass
  
  # integer variable with name
  @abstractmethod
  def intvar(self, n):
    pass
  
  # real variable with name
  @abstractmethod
  def realvar(self, n):
    pass
  
  # logical conjunction
  @abstractmethod
  def land(self, l):
    pass

  # logical disjunction
  @abstractmethod
  def lor(self, l):
    pass

  # logical negation
  @abstractmethod
  def neg(self, a):
    pass

  # logical implication
  @abstractmethod
  def implies(self, a, b):
    pass

  # logical biimplication
  @abstractmethod
  def iff(self, a, b):
    pass

  # equality of arithmetic terms
  @abstractmethod
  def eq(self, a, b):
    pass

  # less-than on arithmetic terms
  @abstractmethod
  def lt(self, a, b):
    pass

  # greater-or-equal on arithmetic terms
  @abstractmethod
  def ge(self, a, b):
    pass

  # increment of arithmetic term by 1
  @abstractmethod
  def inc(self, a):
    pass
  
  # subtraction
  @abstractmethod
  def minus(self, a, b):
    pass

  # addition
  @abstractmethod
  def plus(self, a, b):
    pass

  # if-then-else
  @abstractmethod
  def ite(self, cond, a, b):
    pass

  # minimum of two arithmetic expressions
  @abstractmethod
  def min(self, a, b):
    pass

  @abstractmethod
  def push(self):
    pass

  @abstractmethod
  def pop(self):
    pass

  # add list of assertions
  @abstractmethod
  def require(self):
    pass

  # minimize given expression
  @abstractmethod
  def minimize(self, e):
    pass

  # reset context
  @abstractmethod
  def reset(self):
    pass

  # destroy context
  @abstractmethod
  def destroy(self):
    pass

  @staticmethod
  def shutdown():
    pass


class Model:
  __metaclass__ = ABCMeta

  @abstractmethod
  def __init__(self):
      pass
  
  @abstractmethod
  def eval_bool(self, v):
    pass
  
  @abstractmethod
  def eval_int(self, v):
    pass
  
  @abstractmethod
  def eval_real(self, v):
    pass
  