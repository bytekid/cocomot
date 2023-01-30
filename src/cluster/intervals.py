from sys import maxsize

from dpn.expr import Num, Var

class Interval:
  def __init__(self, l, l_is_open, h, h_is_open):
    self.low = l 
    self.low_open = l_is_open
    self.high = h 
    self.high_open = h_is_open

  def __eq__(self,other):
    if self.low == other.low and self.low_open == other.low_open and\
       self.high == other.high and self.high_open == other.high_open:
      return True
    return False

  def __hash__(self):
      return hash((self.low, self.low_open, self.high, self.high_open))

  def __str__(self):
    lb = "(" if self.low_open else "["
    ub = ")" if self.high_open else "]"
    return lb + str(self.low) + ", " + str(self.high) + ub

  def mem(self, n):
    lb = self.low < n if self.low_open else self.low <= n 
    ub = self.high > n if self.high_open else self.high >= n 
    return lb and ub

  def intersects(self, ival):
    if (self.low == ival.high and (self.low_open or ival.high_open)) or \
      (self.high == ival.low and (self.high_open or ival.low_open)):
      return False
    return self.mem(ival.low) or ival.mem(self.low)

  def split(self, ival):
    if not self.intersects(ival):
      return (set (), { self }, { ival })
    elif self == ival:
      return ({ self }, set(), set())
    elif self.mem(ival.low):
      i1 = Interval(self.low, self.low_open, ival.low, not ival.low_open)
      if self.mem(ival.high): # properly contained
        if ival.high == self.high:
          return ({ ival }, { i1 }, set())
        else:
          i2 = Interval(ival.high, not ival.high_open, self.high, self.high_open)
          return ({ ival }, { i1, i2 }, set())
      else:
        i2 = Interval(ival.low, ival.low_open, self.high, self.high_open)
        if ival.high == self.high:
          return ({i2}, {i1}, set())
        else:
          i3 = Interval(self.high, not self.high_open, ival.high, ival.high_open)
          return ({i2}, {i1}, {i3})
    else:
      (intersect, ival2, self2) = ival.split(self)
      return (intersect, self2, ival2)

def add_split(y, ivals): # assumes ivals intersection-free
  if len(ivals) == 0:
    return { y }
  else:
    x = ivals.pop() # ivals is changed
  if not y.intersects(x):
    return add_split(y, ivals).union({ x })
  else:
    (xy, xrest, yrest) = x.split(y)
    if len(yrest) == 0:
      return ivals.union(xy).union(xrest)
    else:
      while len(yrest) > 0:
        z = yrest.pop()
        ivals =  add_split(z, ivals)
      return ivals.union(xy).union(xrest)


def cmp_interval(c):
  if isinstance(c.left, Var):
    assert(isinstance(c.right, Num))
    b = float(c.right.num)
    var = c.left.basename()
  else:
    assert(isinstance(c.left, Num) and isinstance(c.right, Var))
    b = float(c.left.num)
    var = c.right.basename()
  if c.op == "==" or c.op == "!=": # for intervals, it's the same
    ival =  Interval(b, False, b, False)
  elif c.op == ">=" or c.op == "<":
    ival = Interval(b, False, maxsize, True)
  else:
    assert(c.op == ">" or c.op == "<=")
    ival = Interval(b, True, maxsize, True)
  return (var, ival)

def is_interval_cmp(c):
  return (isinstance(c.left, Var) and isinstance(c.right, Num)) or \
    (isinstance(c.right, Var) and isinstance(c.left, Num)) #FIXME

def comparison_intervals(dpn):
  cmps=set([])
  for t in dpn.transitions():
    if "constraint" in t:
      cmps = cmps.union(t["constraint"].comparisons())

  # collect all variables that only appear in interval comparisons
  vs = [v["name"] for v in dpn.variables()]
  for c in cmps:
    if not is_interval_cmp(c):
      vs = [ v for v in vs if not v in c.vars() ]

  cmp_ivals = [cmp_interval(c) for c in cmps if is_interval_cmp(c) \
    and c.vars().issubset(set(vs)) ]
  var_intervals = {}
  for vname in vs:
    intervals = set([Interval(- maxsize, True, maxsize, True)])
    for (v, ival) in cmp_ivals:
      if v == vname:
        intervals = add_split(ival, intervals)
    var_intervals[vname] = list(intervals)
  return var_intervals
