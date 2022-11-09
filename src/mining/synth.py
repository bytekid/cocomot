from abc import ABCMeta, abstractmethod
import time

from smt.ysolver import YicesSolver
from smt.z3solver import Z3Solver, Z3Model
from utils import *

class ConstraintSynthesizer:
  __metaclass__ = ABCMeta

  @abstractmethod
  def generate(self, var, activity, log):
      pass
  
  @abstractmethod
  def __str__(self):
      pass
  
  @abstractmethod
  def time(self):
      pass
  
  def fitness(self):
    return self._fitness



class BoundSynthesizer(ConstraintSynthesizer):

  def __init__(self, do_read_guard):
    self._do_read_guard = do_read_guard

  def generate(self, v, activity, log):
    self._variable = v
    self._activity = activity
    self._instances = [e for (t, _) in log for e in t \
      if e["label"] == activity]
    self._log = log
    t_start = time.perf_counter()
    select = "valuation" if self._do_read_guard else "written"
    values = [ e[select][v] for e in self._instances if v in e[select] ]
    self._lower = min(values)
    self._upper = max(values)
    self._time = time.perf_counter() - t_start
    suffix = "" if self._do_read_guard else "'"
    self._constraint = "%.2f <= %s%s <= %.2f" % \
      (self._lower, self._variable, suffix, self._upper)
    self._fitness = 1
    self._error = 1

  def __str__(self):
    return self._constraint
  
  def print(self):
    print("  bounds: " + self._constraint)
    print("    time:         %.2f" % self._time)
    #print("    error/subset: %.2f" % self._error)
    #print("    fitness:    %.2f" % self._fitness)
  
  def time(self):
    return self._time



class LinCombSynthesizer(ConstraintSynthesizer):

  string_vals = {}

  def __init__(self, op, do_read_guard):
    self._do_read_guard = do_read_guard
    self._op = op

  def var_type(self, v):
    vals = [(i["valuation"] if self._do_read_guard else i["written"]) \
      for i in self._instances if v in (i["valuation"] if self._do_read_guard else i["written"])]
    #if len(vals) == 0:
    #  print("no vals for " + v)
    return val_type(vals[0][v])

  def val(self, s, val):
    if isinstance(val, int):
      return s.num(val)
    elif isinstance(val, float):
      return s.real(val)
    else:
      if not val in string_vals:
        string_vals[val] = len(string_vals)
      return s.num(string_vals[val])

  def generate(self, v, activity, log):
    self._variable = v
    self._activity = activity
    self._log = log
    self._instances = [e for (t, _) in log for e in t if e["label"] == activity]
    select = "valuation" if self._do_read_guard else "written"
    self._instances = [i for i in self._instances if v in i[select]][:50]
    #for i in self._instances:
    #  print(i)
    t_start = time.perf_counter()
    vtype = self.var_type(v)
    # get variables of same type
    rdeps = set([v for e in self._instances for v in e["valuation"] \
      if val_type(e["valuation"][v]) == vtype])
    wdeps = set() if self._do_read_guard else \
      set([w for e in self._instances for w in e["written"] \
      if val_type(e["written"][w]) == vtype])
    if self._do_read_guard:
      rdeps.remove(v)
    else:
      wdeps.remove(v)
    s = Z3Solver()
    dvars = [ (v, s.realvar(v)) for v in rdeps]
    wvars = [ (v, s.realvar(v+"'")) for v in wdeps]
    zero = s.real(0)
    one = s.real(1)
    total_error = zero
    for (i, e) in enumerate(self._instances):
      written = e["written"]
      read = e["valuation"]
      esum = s.real(0)
      for (name, var) in dvars:
        if name in read:
          summand = s.mult(var, self.val(s, read[name] ))
          esum = s.plus(esum, summand)
      for (name, var) in wvars:
        if name in written:
          summand = s.mult(var, self.val(s, written[name] ))
          esum = s.plus(esum, summand)
      err = s.realvar("err"+str(i))
      the_value = read[v] if self._do_read_guard else written[v]
      if self._op == "==" or self._op == ">=":
        req = s.eq(err, s.minus(self.val(s, the_value), esum))
      else:
        assert(self._op == "<=")
        req = s.eq(err, s.minus(esum, self.val(s, the_value)))
      add_err = s.abs(err) if self._op == "==" else s.ite(s.ge(err, zero), zero, one)

      s.require(req)
      total_error = s.plus(total_error, add_err)
    
    m = s.minimize(total_error, 10000)
    self._time = time.perf_counter() - t_start
    self._error = m.eval_real(total_error)
    dvarcoeff = [ (n, m.eval_real(var)) for (n, var) in dvars \
      if m.eval_real(var) != 0]
    wvarcoeff = [ (n, m.eval_real(var)) for (n, var) in wvars \
      if m.eval_real(var) != 0]
    self.set_constraint_str(dvarcoeff, wvarcoeff)
    self.compute_fitness(dvarcoeff, wvarcoeff)
  
  def compute_fitness(self, dvars, wvars):
    # assume that log is list of (trace, count) pairs
    assignment = "valuation" if self._do_read_guard else "written"

    def check(e):
      val = e[assignment][self._variable]
      for (v, c) in dvars:
        if v not in e["valuation"]:
          return False
        val -= c*e["valuation"][v]
      for (v, c) in wvars:
        if v not in e["written"]:
          return False
        val -= c*e["written"][v]
      return val < 0.01

    events = [e for (t, _) in self._log \
      for e in t if e["label"] == self._activity \
      and self._variable in e[assignment] ]
    sat_cnt = len([ e for e in events if check(e) ])
    # print(" number matching %d of %d" % (sat_cnt, len(events)))
    self._fitness = float(sat_cnt) / float(len(events))
      
  
  def set_constraint_str(self, dvars, wvars):
    s = ""
    for (n, coeff) in dvars + [(n+"'",w) for (n,w) in wvars]:
      coeffstr = "" if coeff == 1 else ("%.2f*" % coeff)
      s += ("" if len(s) == 0 else " + ") + coeffstr + n
    s = "0" if len(s) == 0 else s
    suffix = "" if self._do_read_guard else "'"
    self._constraint = "%s%s %s %s" % (self._variable, suffix, self._op, s)


  def __str__(self):
    return self._constraint
  
  def print(self):
    print("  linear combination: " + self._constraint)
    print("    time:         %.2f" % self._time)
    print("    error/subset: %.2f" % self._error)
    print("    fitness:    %.4f" % self._fitness)
  
  def time(self):
    return self._time


class SMTFunctionSynthesizer(ConstraintSynthesizer):

  string_vals = {}

  def __init__(self):
    self._error = False
    self._fitness = 0

  def val_sort(self, s, val):
    vtype = s.get_bool_sort() if isinstance(val, bool) else \
      s.get_int_sort() if isinstance(val, int) else s.get_real_sort() \
      if isinstance(val, float) else s.get_int_sort()
    return vtype

  def smt_sort(self, s, v):
    vals = [i["valuation"] for i in self._instances if v in i["valuation"]]
    return self.val_sort(s, vals[0][v])

  def val(self, s, val, vsort):
    if vsort == s.get_bool_sort():
      return s.true() if val else s.neg(s.true())
    elif vsort == s.get_int_sort() and isinstance(val, int):
      return s.num(val)
    elif vsort == s.get_real_sort():
      return s.real(val)
    else:
      if not val in self.string_vals:
        self.string_vals[val] = len(self.string_vals)
      return s.num(self.string_vals[val])

  def generate(self, v, activity, log):
    self._variable = v
    self._activity = activity
    self._log = log
    self._instances = [e for (t, _) in log for e in t if e["label"] == activity]
    self._instances = [i for i in self._instances if v in i["written"]][:50]
    t_start = time.perf_counter()

    s = Z3Solver()
    res_sort = self.val_sort(s, self._instances[0]["written"][v])
    self._vsort = res_sort
    rdeps = set([(v, self.smt_sort(s, v)) \
      for e in self._instances for v in e["valuation"]])
    if len(rdeps) == 0:
      self._error = True
      return
    #print("f" + v, [s for (_,s) in rdeps], res_sort)
    f = s.mk_fun("f" + v, [s for (_,s) in rdeps], res_sort)

    total_error = s.num(0)
    for (i, e) in enumerate(self._instances):
      read = e["valuation"]
      written = e["written"]
      if not all(v in read for (v, vtype) in rdeps ):
        continue
      args = [self.val(s, read[v], vtype) for (v, vtype) in rdeps]
      
      err = s.realvar("err"+str(i))
      #print(f, args)
      equal = s.eq(s.apply_fun(f, args), self.val(s, written[v], res_sort))
      s.require(s.eq(err, s.ite(equal, s.num(0), s.num(1))))
      total_error = s.plus(total_error, s.abs(err))
    
    m = s.minimize(total_error, 10000)
    self._time = time.perf_counter() - t_start
    self._error = m.eval_real(total_error)
    self._thefunction = str(m.model[f])
    self.compute_fitness(f, rdeps, s, m)

  def compute_fitness(self, f, rdeps, s, m):

    def check(e):
      if not all(v in e["valuation"] for (v, _) in rdeps ):
        return False
      args = [self.val(s, e["valuation"][v], vtype) for (v, vtype) in rdeps]
      value = self.val(s, e["written"][self._variable], self._vsort)
      return m.eval_bool(s.eq(s.apply_fun(f, args), value))

    events = [e for (t, _) in self._log \
      for e in t if e["label"] == self._activity \
      and self._variable in e["written"] ]
    sat_cnt = len([ e for e in events if check(e) ])
    # print(" number matching %d of %d" % (sat_cnt, len(events)))
    self._fitness = float(sat_cnt) / float(len(events))

  def print(self):
    if self._error:
      print("  function: ?")
    else:
      fstr = self._thefunction if self._fitness > .9 else "..."
      print("  function: " + fstr)
      print("    time:         %.2f" % self._time)
      print("    error/subset: %.2f" % self._error)
      print("    fitness:    %.4f" % self._fitness)