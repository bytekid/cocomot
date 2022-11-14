from xml.dom.minidom import getDOMImplementation
import xml.dom.minidom


class Indeterminacy:
  def __init__(self, value):
    self._value = value

  def is_uncertain(self):
    return self._value < 1

  def __str__(self):
    return ("?" + str(self._value)) if self.is_uncertain() else "!"

  def to_xes(self, doc):
    #  <container key="uncertainty:entry">
    #    <bool key="uncertainty:indeterminacy" value="true" />
    #    <float key="uncertainty:probability" value=".8" />
    #  </container>
    # only supposed to be called if self.is_uncertain()
    xcont = doc.createElement("container")
    xbool = doc.createElement("bool")
    xbool.setAttribute("key", "uncertainty:indeterminacy");
    xbool.setAttribute("value", "true");
    xcont.appendChild(xbool)
    xbool = doc.createElement("float")
    xbool.setAttribute("key", "uncertainty:probability");
    xbool.setAttribute("value", str('{:04.2f}'.format(self._value)));
    xcont.appendChild(xbool)
    return xcont


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
  
  def to_xes(self, doc):
    #
    #  <list key="uncertainty:discrete_weak">
    #    <values>
    #      <container key="uncertainty:entry">
    #        <string key="concept:name" value="a"/>
    #        <float key="uncertainty:probability" value="0.25" />
    #      </container>
    #      <container key="uncertainty:entry">
    #        <string key="concept:name" value="b"/>
    #        <float key="uncertainty:probability" value="0.75" />
    #      </container>
    #    </values>
    #  </list>
    if self.is_uncertain():
      xact = doc.createElement("list")
      xact.setAttribute("key", "uncertainty:discrete_weak");
      xvals = doc.createElement("values")
      for (a,p) in self._activities.items():
        xcont = doc.createElement("container")
        xcont.setAttribute("key", "uncertainty:entry");
        xstr = doc.createElement("string")
        xstr.setAttribute("key", "concept:name");
        xstr.setAttribute("value", a);
        xcont.appendChild(xstr)
        xprob = doc.createElement("float")
        xprob.setAttribute("key", "uncertainty:probability");
        xprob.setAttribute("value", str('{:04.2f}'.format(p)));
        xcont.appendChild(xprob)
        xvals.appendChild(xcont)
      xact.appendChild(xvals)
      return xact
    else:
      xstr = doc.createElement("string")
      xstr.setAttribute("key", "concept:name");
      xstr.setAttribute("value", list(self._activities.keys())[0]);
      return xstr



class UncertainTimestamp:
  def __init__(self, lower, upper=None):
    self._lower = lower
    self._upper = upper 

  def is_uncertain(self):
    return self._upper != None

  def __str__(self):
    if self.is_uncertain():
      return "[" + str(self._lower) + ", " + str(self._upper) + "]"
    else:
      return str(self._lower)

  def fix(self, t):
    assert(self._lower <= t and (self._upper == None or t <= self._upper))
    self._lower = t
    self._upper = t
  

  def to_xes(self, doc):
    xs = []
    #<date key="time:timestamp" value="2021-04-26T18:46:40.050+00:00"/>
    #<date key="uncertainty:time:timestamp_max" value="2021-04-26T22:46:40.050+00:00"/>
    xtime = doc.createElement("date")
    xtime.setAttribute("key", "time:timestamp")
    timeformat = "%Y-%m-%dT%H:%M:%S%z"
    xtime.setAttribute("value", self._lower.strftime(timeformat) )
    xs.append(xtime)
    if self.is_uncertain():
      xtimeu = doc.createElement("date")
      xtimeu.setAttribute("key", "uncertainty:time:timestamp_max")
      xtimeu.setAttribute("value", self._upper.strftime(timeformat))
      xs.append(xtimeu)
    return xs


class UncertainDataValue:
  def __init__(self, kind, name, values=None, lower=None, upper=None):
    assert(values!=None or (lower != None and upper != None and lower < upper))
    assert(values==None or (lower == None and upper == None))
    self._kind = kind
    self._name = name
    if values != None:
      self._values = values # map value  to probability
      assert(len(values) > 0)
    else:
      self._lower = lower
      self._upper = upper

  def __str__(self):
    if self._values != None:
      s = self._name + " {"
      for v in self._values:
        s += str(v) + ", "
      return s[:-2] + "}"
    else:
      return "[" + self._lower + ", " + self._upper + "]"


  def to_xes(self, doc):
    if self._values != None:
      if len(self._values) > 1: # so event is really uncertain
        #	<list key="uncertainty:discrete_strong">
        #		<values>
        #			<string key="amount" value="10.0"/>
        #			<string key="amount" value="15.0"/>
        #		</values>
        #	</list>
        xlist = doc.createElement("list")
        xlist.setAttribute("key", "uncertainty:discrete_strong")
        xvals = doc.createElement("values")
        xlist.appendChild(xvals)
        for v in self._values:
          xval = doc.createElement(self._kind)
          xval.setAttribute("key", self._name)
          xval.setAttribute("value", str(v))
          xvals.appendChild(xval)
        return xlist
      else:
        xval = doc.createElement(self._kind)
        xval.setAttribute("key", self._name)
        xval.setAttribute("value", str(self._values[0]))
        return xval
    else:
      #	<list key="uncertainty:continuous_strong">
      #		<uncertainty:lower:bound>
      #			<string key="amount" value="5.0"/>
      #		</uncertainty:lower:bound>
      #		<uncertainty:upper:bound>
      #			<string key="amount" value="10.0"/>
      #		</uncertainty:upper:bound>
      #	</list>
      xlist = doc.createElement("list")
      xlist.setAttribute("key", "uncertainty:continuous_strong")
      lname, uname = "uncertainty:lower:bound", "uncertainty:upper:bound"
      for (name, v) in [(lname, self._lower), (uname, self._upper)]:
        xbound = doc.createElement("value")
        xbound.setAttribute("key", name)
        xval = doc.createElement(self._kind)
        xval.setAttribute("key", self._name)
        xval.setAttribute("value", str(v))
        xbound.appendChild(xval)
        xlist.appendChild(xbound)




class UncertainEvent:
  
  id_counter = 0

  def __init__(self, indeterminacy, activity, time, data):
    self._indet = indeterminacy
    assert(isinstance(indeterminacy, Indeterminacy))
    self._activity = activity
    assert(isinstance(activity, UncertainActivity))
    self._time = time
    assert(isinstance(time, UncertainTimestamp))
    self._data = dict([ (d._name, d) for d in data]) # data is UncertainDataValue list
    self._id = UncertainEvent.id_counter
    UncertainEvent.id_counter += 1

  def __str__(self):
    d = "["
    for v in self._data.values():
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
  
  def data(self):
    return self._data
  
  def has_values(self, name):
    return name in self._data
  
  def values(self, name):
    return self._data[name]._values

  def set_indeterminacy(self, indet):
    self._indet = indet

  def set_uncertain_time(self, t):
    self._time = t

  def set_uncertain_activity(self, a):
    self._activity = a

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
    valuation = dict([ (d._name, d._values[0]) for d in self._data.values() ])
    return {
      "label": list(self._activity._activities.keys())[0],
      "time": self._time._lower,
      "valuation": valuation
    }

  def to_xes(self, doc):
    xevent = doc.createElement('event')
    xevent.appendChild(self._activity.to_xes(doc))
    for xtime in self._time.to_xes(doc):
      xevent.appendChild(xtime)
    for dvar in self._data.values():
      xevent.appendChild(dvar.to_xes(doc))
    if self._indet.is_uncertain():
      xevent.appendChild(self._indet.to_xes(doc))
    return xevent


class UncertainTrace:
  def __init__(self, events):
    self._events = events
    #self.normalize_time()

  def normalize_time(self):
    # replace all times by float values for simpler treatment in encoding
    events = self._events
    times = [e.lower_time() for e in events] + \
      [e.upper_time() for e in events if e.upper_time() != None]
    times = dict([ (t,i) for (i, t) in enumerate(sorted(times)) ])
    for e in events:
      e._time._lower = float(times[e._time._lower])
      e._time._upper = float(times[e._time._upper]) if e._time._upper else None

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

  def to_xes(self, doc):
    xtrace = doc.createElement('trace')
    for event in self._events:
      xevent = event.to_xes(doc)
      xtrace.appendChild(xevent)
    return xtrace


class UncertainLog:

  def __init__(self, traces):
    self._traces = traces

  def to_xes(self):
    doc = xml.dom.minidom.parseString("<log/>")
    root = doc.documentElement
    root.setAttribute("xes.version", "1849-2016")
    root.setAttribute("xes.features", "nested-attributes")
    root.setAttribute("xmlns", "http://www.xes-standard.org/")
    for trace in self._traces:
      xtrace = trace.to_xes(doc)
      root.appendChild(xtrace)
    return root
