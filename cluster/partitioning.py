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
    logsp = [ (t, NaivePartitioning.trace_data(t)) for t in logs ]
    logsp = sorted(logsp, key=lambda t: t[1])
    i = 0
    self.partitions = []
    while i < len(logsp):
      (trace, tdata) = logsp[i]
      j = i + 1
      while j < len(logsp) and logsp[j][1] == tdata:
        j += 1
      self.partitions.append((trace, j - i))
      i = j

  def representatives(self):
    return [ t for (t,_) in self.partitions ]

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
    logsp = [ (t, self.trace_profile(t, dpn, cmps)) for t in logs ]
    logsp = sorted(logsp, key=lambda t: t[1])
    i = 0
    self.partitions = []
    while i < len(logsp):
      (trace, profile) = logsp[i]
      j = i + 1
      #if j < len(logsp) and logsp[j][1] == profile and len(trace) == len(logsp[j][0]) and len(trace) == 3:
        #print("EQUIVALENT %d" % len(self.partitions))
        #print(trace)
        #print(profile)
        #print(logsp[j][0])
        #print(logsp[j][1])
      while j < len(logsp) and logsp[j][1] == profile:
        j += 1
      self.partitions.append((trace, j - i))
      i = j

  def representatives(self):
    return [ t for (t,_) in self.partitions ]

  def partition_count(self):
    return len(self.partitions)
