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
      self._activities = arg # map activity name to probability
      assert(len(arg) > 0)

  def is_uncertain(self):
    return len(self._activities) > 1

  def labels(self):
    return self._activities.keys()

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
  def __init__(self, indeterminacy, activity, time, data):
    self._indet = indeterminacy
    assert(isinstance(indeterminacy, Indeterminacy))
    self._activity = activity
    assert(isinstance(activity, UncertainActivity))
    self._time = time
    assert(isinstance(time, UncertainTimestamp))
    self._data = data # UncertainDataValue list

  def __str__(self):
    d = "["
    for v in self._data:
      d += str(v) + ", "
    return "<" + str(self._indet) + ", " + str(self._activity) + ", " + \
      str(self._time) + ", " + d + "] >"
  
  def is_indeterminate(self):
    return self._indet._value < 1
  
  def labels(self):
    return self._activity.labels()

class UncertainTrace:
  def __init__(self, events):
    self._events = events

  def __str__(self):
    s = "{\n"
    for e in self._events:
      s += " " + str(e) + "\n"
    return s + "}"

  def __len__(self):
    return len(self._events)