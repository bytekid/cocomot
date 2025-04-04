from cluster.intervals import comparison_intervals

# naive partitioning filters considers traces equivalent if they have the same
# activity sequence and the same valuation


class NaivePartitioning:

  @staticmethod
  def trace_data(t):
    d = [len(t)]
    def event_data(e):
      return [e["label"]] + list(e["valuation"].items())
    return d + [event_data(e) for e in t]

  def __init__(self, logs):
    logsp = [ (t, NaivePartitioning.trace_data(t), cnt) for (t, cnt) in logs ]
    logsp = sorted(logsp, key=lambda t: t[1])
    i = 0
    self.partitions = []
    while i < len(logsp):
      (trace, tdata, cnt) = logsp[i]
      j = i + 1
      while j < len(logsp) and logsp[j][1] == tdata:
        cnt += logsp[j][2]
        j += 1
      self.partitions.append((trace, cnt))
      i = j

  def representatives(self):
    return self.partitions

  def partition_count(self):
    return len(self.partitions)


class IntervalPartitioning:

  @staticmethod
  def trace_profile(trace, dpn, cmpclasses):
    def cmpclass(x, n):
      if not x in cmpclasses:
        return n
      for (i,ival) in enumerate(cmpclasses[x]):
        if ival.mem(n):
          return i+1
      return 0
    
    length = len(trace)
    varnames = [v["name"] for v in dpn.variables()]
    prof = []
    for e in trace:
      written = e["valuation"]
      vs = [ cmpclass(v, written[v] if v in written else 0) for v in varnames ]
      prof.append((e["label"], vs))
    return (length, prof)

  def __init__(self, dpn, logs):
    cmps = comparison_intervals(dpn)
    logsp = [ (t, self.trace_profile(t, dpn, cmps), cnt) for (t, cnt) in logs ]
    logsp = sorted(logsp, key=lambda t: t[1])
    i = 0
    self.partitions = []
    while i < len(logsp):
      (trace, profile, cnt) = logsp[i]
      j = i + 1
      while j < len(logsp) and logsp[j][1] == profile:
        cnt += logsp[j][2]
        j += 1
      self.partitions.append((trace, cnt))
      i = j
      self._cmps = cmps
      self._dpn = dpn
    
  def equivalent(self, t1, t2):
    dpn = self._dpn
    cmps = self._cmps
    return self.trace_profile(t1, dpn, cmps) == self.trace_profile(t2, dpn, cmps)

  def representatives(self):
    return self.partitions

  def partition_count(self):
    return len(self.partitions)
