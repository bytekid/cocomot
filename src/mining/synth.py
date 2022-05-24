from abc import ABCMeta, abstractmethod
import time

from smt.ysolver import YicesSolver
from smt.z3solver import Z3Solver, Z3Model

class ConstraintSynthesizer:
  __metaclass__ = ABCMeta

  @abstractmethod
  def generate(self, var, events):
      pass
  
  @abstractmethod
  def __str__(self):
      pass
  
  @abstractmethod
  def time(self):
      pass
  
  @abstractmethod
  def precision(self):
      pass



class BoundSynthesizer(ConstraintSynthesizer):

  def __init__(self, do_read_guard):
    self._do_read_guard = do_read_guard

  def generate(self, v, activity, instances, log):
    self._variable = v
    self._activity = activity
    self._instances = instances
    self._log = log
    t_start = time.perf_counter()
    select = "valuation" if self._do_read_guard else "written"
    values = [ e[select][v] for e in instances if v in e[select] ]
    self._lower = min(values)
    self._upper = max(values)
    self._time = time.perf_counter() - t_start
    suffix = "" if self._do_read_guard else "'"
    self._constraint = "%.2f <= %s%s <= %.2f" % \
      (self._lower, self._variable, suffix, self._upper)
    self._precision = 1
    self._error = 1

  def __str__(self):
    return self._constraint
  
  def print(self):
    print("  bounds: " + self._constraint)
    print("    time:         %.2f" % self._time)
    #print("    error/subset: %.2f" % self._error)
    #print("    precision:    %.2f" % self._precision)
  
  def time(self):
    return self._time
  
  def precision(self):
    return self._precision



class LinCombSynthesizer(ConstraintSynthesizer):

  def __init__(self, do_read_guard):
    self._do_read_guard = do_read_guard

  def generate(self, v, activity, instances, log):
    self._variable = v
    self._activity = activity
    self._instances = instances
    self._log = log
    t_start = time.perf_counter()
    is_float = lambda value: isinstance(value, float)
    rdeps = set([v for e in instances for v in e["valuation"] if is_float(e["valuation"][v])])
    wdeps = set() if self._do_read_guard else \
      set([v for e in instances for v in e["written"] if is_float(e["written"][v])])
    if self._do_read_guard:
      rdeps.remove(v)
    else:
      wdeps.remove(v)
    s = Z3Solver()
    dvars = [ (v, s.realvar(v)) for v in rdeps]
    wvars = [ (v, s.realvar(v+"'")) for v in wdeps]
    total_error = None
    for (i, e) in enumerate(instances):
      written = e["written"]
      read = e["valuation"]
      if (v not in written and not self._do_read_guard) or \
         (v not in read and self._do_read_guard):
        continue
      esum = None
      for (name, var) in dvars:
        if name in read:
          summand = s.mult(var, s.real(read[name]))
          esum = s.plus(esum, summand) if esum != None else summand
      for (name, var) in wvars:
        if name in written:
          summand = s.mult(var, s.real(written[name]))
          esum = s.plus(esum, summand) if esum != None else summand
      err = s.realvar("err"+str(i))
      the_value = read[v] if self._do_read_guard else written[v]
      s.require(s.eq(err, s.minus(s.real(the_value), esum)))
      error = s.abs(err)
      #s.require([s.eq(error, s.num(0))])
      total_error = error if total_error == None else s.plus(total_error, error)
    
    m = s.minimize(total_error, 10000)
    self._time = time.perf_counter() - t_start
    self._error = m.eval_real(total_error)
    dvarcoeff = [ (n, m.eval_real(var)) for (n, var) in dvars \
      if m.eval_real(var) != 0]
    wvarcoeff = [ (n, m.eval_real(var)) for (n, var) in wvars \
      if m.eval_real(var) != 0]
    self.set_constraint_str(dvarcoeff, wvarcoeff)
    self.compute_precision(dvarcoeff, wvarcoeff)
  
  def compute_precision(self, dvars, wvars):
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
      return val < 0.1

    events = [e for (t, _) in self._log \
      for e in t if e["label"] == self._activity \
      and self._variable in e[assignment] ]
    sat_cnt = len([ e for e in events if check(e) ])
    self._precision = float(sat_cnt) / float(len(events))
      
  
  def set_constraint_str(self, dvars, wvars):
    s = ""
    for (n, coeff) in dvars + [(n+"'",w) for (n,w) in wvars]:
      coeffstr = "" if coeff == 1 else ("%.2f*" % coeff)
      s += ("" if len(s) == 0 else " + ") + coeffstr + n
    s = "0" if len(s) == 0 else s
    suffix = "" if self._do_read_guard else "'"
    self._constraint = "%s%s = %s" % (self._variable, suffix, s)


  def __str__(self):
    return self._constraint
  
  def print(self):
    print("  linear combination: " + self._constraint)
    print("    time:         %.2f" % self._time)
    print("    error/subset: %.2f" % self._error)
    print("    precision:    %.2f" % self._precision)
  
  def time(self):
    return self._time
  
  def precision(self):
    return self._precision
