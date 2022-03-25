class Indeterminacy:
  def __init__(self, value):
    self._value = value

  def __str__(self):
    return ("?" + str(self._value)) if self._value < 1 else "!"


class UncertainActivity:
  def __init__(self, arg):
    if isinstance(arg, str):
      self._activities = {arg:1}
    else:
      self._activities = {} # map activity name to probability
      for (a,p) in arg.items():
        self._activities[a] = float(p)
      assert(len(arg) > 0)

  def is_uncertain(self):
    return len(self._activities) > 1

  def labels(self):
    return self._activities.keys()

  def fix(self, a):
    assert(a in self._activities.keys())
    self._activities = {a:1}

  def __str__(self):
    if not self.is_uncertain():
      return list(self._activities.keys())[0]
    else:
      s = "["
      for (a,p) in self._activities.items():
        s += a + ":" + str(p) + ", "
      return s[:-2] + "]"


class UncertainTimestamp:
  def __init__(self, lower, upper=None):
    self._lower = lower
    self._upper = upper if upper != None else lower

  def is_uncertain(self):
    return self._lower != self._upper

  def __str__(self):
    if self.is_uncertain():
      return "[" + str(self._lower) + ", " + str(self._upper) + "]"
    else:
      return str(self._lower)

  def fix(self, t):
    assert(self._lower <= t and t <= self._upper)
    self._lower = t
    self._upper = t


class UncertainDataValue:
  def __init__(self, name, values):
    self._name = name
    self._values = values # map value  to probability
    assert(len(values) > 0)

  def __str__(self):
    s = self._name + " ["
    for v in self._values:
      s += str(v) + ", "
    return s[:-2] + "]"


class UncertainEvent:
  
  id_counter = 0

  def __init__(self, indeterminacy, activity, time, data):
    self._indet = indeterminacy
    assert(isinstance(indeterminacy, Indeterminacy))
    self._activity = activity
    assert(isinstance(activity, UncertainActivity))
    self._time = time
    assert(isinstance(time, UncertainTimestamp))
    self._data = dict(data) # UncertainDataValue list
    self._id = UncertainEvent.id_counter
    UncertainEvent.id_counter += 1

  def __str__(self):
    d = "["
    for v in self._data:
      d += str(v) + ", "
    return "<" + str(self._indet) + ", " + str(self._activity) + ", " + \
      str(self._time) + ", " + d + "] >"
  
  def is_uncertain(self):
    return self._indet._value < 1
  
  def has_uncertain_time(self):
    return self._time.is_uncertain()
  
  def upper_time(self):
    return self._time._upper
  
  def indeterminacy(self):
    return self._indet._value
  
  def lower_time(self):
    return self._time._lower
  
  def labels(self):
    return self._activity.labels()
  
  def values(self, name):
    return self._data[name]

  def fix_determinacy(self):
    self._indet._value = 1

  def fix_label(self, a):
    self._activity.fix(a)

  def fix_time(self, t):
    self._time.fix(t)
  
  def project(self):
    # return standard event as dictionary
    # by the time of the call, all relevant uncertainties should be removed,
    # so take arbitrary admissible value
    valuation = dict([ (d._name, d._values[0]) for d in self._data ])
    return {
      "label": list(self._activity._activities.keys())[0],
      "time": self._time._lower,
      "valuation": valuation
    }

class UncertainTrace:
  def __init__(self, events):
    self._events = events
    self.normalize_time()

  def normalize_time(self):
    # replace all times by float values for simpler treatment in encoding
    events = self._events
    times = [e.lower_time() for e in events] + [e.upper_time() for e in events]
    times = dict([ (t,i) for (i, t) in enumerate(sorted(times)) ])
    for e in events:
      e._time._lower = float(times[e._time._lower])
      e._time._upper = float(times[e._time._upper])

  def has_uncertain_time(self):
    return any( e.has_uncertain_time() for e in self._events )

  def drop(self, key):
    del self._events[key]

  def __str__(self):
    s = "{\n"
    for e in self._events:
      s += " " + str(e) + "\n"
    return s + "}"

  def __len__(self):
    return len(self._events)

  def __getitem__(self, key):
    return self._events[key]
