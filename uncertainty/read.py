from xml.dom import minidom
from html import unescape

ACTIVITY_KEY = "concept:name"
TIMESTAMP_KEY = "time:timestamp"


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
  

class UncertainTrace:
  def __init__(self, events):
    self._events = events

  def __str__(self):
    s = "{\n"
    for e in self._events:
      s += " " + str(e) + "\n"
    return s + "}"

def xes(logfile):
  children = \
    lambda d: [c for c in d.childNodes if c.nodeType == c.ELEMENT_NODE]

  dom = minidom.parse(logfile)
  log = []
  for dom_trace in dom.getElementsByTagName('trace'):
    trace = []
    for dom_event in dom_trace.getElementsByTagName('event'):
      indet = Indeterminacy(1)
      activity = None
      time_lower = None
      time_upper = None
      data = []
      for child in children(dom_event):
        key = child.getAttribute('key')
        if key == ACTIVITY_KEY:
          activity = UncertainActivity(child.getAttribute('value'))
        elif key == "time:timestamp":
          time_lower = child.getAttribute('value')
        elif key == "uncertainty:time:timestamp_max":
          time_upper = child.getAttribute('value')
        elif key == "uncertainty:entry":
          indet_data = children(child)
          for d in indet_data:
            if d.getAttribute('key') == "uncertainty:probability":
              indet = Indeterminacy(float(d.getAttribute('value')))
        elif key == "uncertainty:discrete_weak":
          values = children(child)[0]
          # data or concept:name
          acts = {}
          data_values = []
          data_name = None
          for e in children(values):
            ekey = e.getAttribute('key')
            if ekey == "uncertainty:entry": # activities
              activity = None
              probability = None
              for ee in children(e):
                if ee.getAttribute('key') == "concept:name":
                  activity = ee.getAttribute('value')
                if ee.getAttribute('key') == "uncertainty:probability":
                  probability = ee.getAttribute('value')
              acts[activity] = probability
            else: # data
              data_name = ekey
              data_values.append(e.getAttribute('value'))
          if len(acts) > 0:
            activity = UncertainActivity(acts)
          if len(data_values) > 0:
            data.append(UncertainDataValue(data_name, data_values))
            
      time = UncertainTimestamp(time_lower, time_upper)
      event = UncertainEvent(indet, activity, time, data)
      trace.append(event)
    print(UncertainTrace(trace))
    log.append(UncertainTrace(trace))
