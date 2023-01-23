from xml.dom.minidom import getDOMImplementation
import xml.dom.minidom
from datetime import datetime, timedelta
from copy import deepcopy
from functools import reduce


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
    xcont.setAttribute("key", "uncertainty:entry")
    xbool = doc.createElement("bool")
    xbool.setAttribute("key", "uncertainty:indeterminacy")
    xbool.setAttribute("value", "true")
    xcont.appendChild(xbool)
    xbool = doc.createElement("float")
    xbool.setAttribute("key", "uncertainty:probability")
    xbool.setAttribute("value", str('{:04.2f}'.format(self._value)))
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
    self._upper = upper if upper else lower

  def is_uncertain(self):
    return self._upper != self._lower

  def __str__(self):
    if self.is_uncertain():
      return "[" + str(self._lower) + ", " + str(self._upper) + "]"
    else:
      return str(self._lower)

  def fix(self, t):
    assert(self._lower <= t and t <= self._upper)
    self._lower = t
    self._upper = t

  def set(self, t):
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

stringvalues = {}

def to_num(v):
  if v == "false":
    return 0
  if v == "true":
    return 1
  try:
    return float(v)
  except ValueError: # character
    if v in stringvalues:
      return stringvalues[v]
    else:
      k = len(stringvalues)
      stringvalues[v] = k
      return k

class UncertainDataValue:
  # use either parameter values for discrete list of values, or upper and lower
  # for interval
  def __init__(self, kind, name, values=None, lower=None, upper=None):
    assert(values!=None or (lower != None and upper != None))
    assert(values==None or (lower == None and upper == None))
    assert(values == None or len(values) > 0)
    self._kind = kind
    self._name = name
    # map value  to probability
    self._values = [to_num(v) for v in values] if values else None
    self._lower = to_num(lower) if lower else None
    self._upper = to_num(upper) if upper else None

  def kind(self):
    return self._kind

  def is_discrete(self):
    return self._lower == None

  def is_uncertain(self):
    if self._lower != None:
      return self._lower != self._upper
    else:
      return len(self._values) > 1

  def values(self):
    assert(self.is_discrete())
    return self._values

  def bounds(self):
    assert(not self.is_discrete())
    return (self._lower, self._upper)

  def fix_if_admissible(self, val):
    if self.is_discrete():
      if str(val) in self._values:
        self._values = [val]
      else:
        self._values = [self._values[0]]
    else:
      if not (self._lower <= val and val <= self._upper):
        val = self._lower
      self._lower = val
      self._upper = val

  def admissible(self): # get some admissible value
    return self._values[0] if self.is_discrete() else self._lower

  def __str__(self):
    if self.is_discrete():
      s = self._name + " {"
      for v in self._values:
        s += str(v) + ", "
      return s[:-2] + "}"
    else:
      return "[" + str(self._lower) + ", " + str(self._upper) + "]"


  def to_xes(self, doc):
    if self.is_discrete():
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
      return xlist


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

  @staticmethod
  def from_certain_event(e, time):
    indet = Indeterminacy(1)
    activity = UncertainActivity(e["label"])
    data = []
    for (var,val) in e["valuation"].items():
      dtype = "int" if not ("." in str(val)) else "float"
      data.append(UncertainDataValue(dtype, var, values=[val]))
    utime = UncertainTimestamp(time)
    return UncertainEvent(indet, activity, utime, data)

  def __eq__(self, other):
    return str(self) == str(other) # not efficient but sufficient for now

  def __str__(self):
    d = "["
    for v in self._data.values():
      d += str(v) + ", "
    return "<" + str(self._indet) + ", " + str(self._activity) + ", " + \
      str(self._time) + ", " + d + "] >"

  def is_uncertain(self):
    return self._indet._value < 1

  def has_uncertain_activity(self):
    return self._activity.is_uncertain()

  def has_uncertain_data(self):
    return any(d.is_uncertain() for d in self._data)
  
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
  
  # whether this event has variable set
  def has_data_variable(self, variable):
    return variable in self._data
  
  def data_variable(self, name):
    return self._data[name]

  def set_indeterminacy(self, indet):
    self._indet = indet

  def set_uncertain_time(self, t):
    self._time = t

  def set_uncertain_activity(self, a):
    self._activity = a

  def set_data(self, name, ud):
    self._data[name] = ud

  def fix_determinacy(self):
    self._indet._value = 1

  def fix_label(self, a):
    self._activity.fix(a)

  def fix_time(self, t):
    self._time.fix(t)

  def fix_data(self, valuation):
    for n in self._data:
      if not n in valuation: # irrelevant fields?
        self._data[n].fix_if_admissible(self._data[n].admissible())
      else:
        self._data[n].fix_if_admissible(valuation[n])
  
  def project(self):
    # return standard event as dictionary
    # by the time of the call, all uncertainties should be removed,
    # so take arbitrary admissible value
    valuation = dict([ (n, d.admissible()) for (n, d) in self.data().items() ])
    return {
      "label": list(self._activity._activities.keys())[0],
      "time": self._time._lower,
      "valuation": valuation
    }

  # return all realizations wrt activity and data values (assumed discrete)
  def get_realizations(self):
    assert(not self.has_uncertain_time() and not self.is_uncertain())
    assert(all(x.is_discrete() for x in self._data.values()))
    acts = self._activity._activities.keys()
    vals = [[]]
    for x in self._data.keys():
      vals = [ v + [(x, a)] for v in vals for a in self._data[x]._values]
    reals = []
    for a in acts:
      for val in vals:
        e = deepcopy(self)
        e.fix_data(val)
        e.fix_label(a)
        reals.append(e)
    return reals

  def to_xes(self, doc):
    xevent = doc.createElement('event')
    xevent.appendChild(self._activity.to_xes(doc))
    for xtime in self._time.to_xes(doc):
      xevent.appendChild(xtime)
    for dvar in self.data().values():
      xevent.appendChild(dvar.to_xes(doc))
    if self._indet.is_uncertain():
      xevent.appendChild(self._indet.to_xes(doc))
    return xevent


class UncertainTrace:
  def __init__(self, events):
    self._events = events

  @staticmethod
  def from_certain_trace(events):
    time = datetime.strptime("2021-01-01T00:00:00", "%Y-%m-%dT%H:%M:%S")
    ues = []
    for e in events:
      ue = UncertainEvent.from_certain_event(e, time)
      time = time + timedelta(days=3)
      ues.append(ue)
    return UncertainTrace(ues)

  # called before encoding
  def normalize_time(self):
    # replace all times by float values for simpler treatment in encoding
    events = self._events
    times = [e.lower_time() for e in events] + \
      [e.upper_time() for e in events if e.upper_time() != None]
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

  def get_realizations(self):
    combs = [[]]
    # fix confidence
    for e in self._events:
      if e.is_uncertain():
        e.fix_determinacy()
        combs = combs + [ r + [e] for r in combs]
      else:
        combs = [ r + [e] for r in combs]
    # fix timestamps
    eventseqs = []
    for comb in combs:
      seqs = [[]]
      for enew in comb:
        seqsx = []
        for seq in seqs:
          # interleave enew into seq
          # split into (subseq before, subseq afterwards)
          prepost = [ (seq[0:i], seq[i:]) for i in range(0, len(seq)+1)]
          estr = lambda e: "[" + str(e.lower_time()) + ", " + str(e.upper_time())  + "]"
          seqstr = lambda l: reduce(lambda x,y: x+y,[estr(e) for e in l], "")
          for (pre, post) in prepost:
            
            if (len(pre) > 0 and pre[-1].lower_time() > enew.upper_time()) or \
               (len(post) > 0 and post[0].upper_time() < enew.lower_time()):
               continue # thanks to invariant below this is complete check
            #print("insert", estr(enew), "into", len(pre), len(post), seqstr(pre), seqstr(post))
            #if len(pre) > 0:
            #  print(pre[-1].lower_time(), ">", enew.upper_time(), pre[-1].lower_time() > enew.upper_time())
            ex = deepcopy(enew)
            # maintain invariant that new elements lb is not smaller than prev
            # element's lb, and next element's upper bound is not higher
            if len(pre) > 0:
              pre = deepcopy(pre)
              l = max(ex.lower_time(), pre[-1].lower_time())
              ex._time._lower = min(ex.upper_time(), l)
              u = min(ex.upper_time(), pre[-1].upper_time())
              pre[-1]._time._upper = max(u, pre[-1].lower_time())
              assert(pre[-1].lower_time() <= pre[-1].upper_time())
            if len(post) > 0:
              post = deepcopy(post)
              u = min(ex.upper_time(), post[0].upper_time())
              ex._time._upper = max(u,ex.lower_time())
              l = max(ex.lower_time(), post[0].lower_time())
              post[0]._time._lower = min(l, post[0].upper_time())
              assert(post[0].lower_time() <= post[0].upper_time())
            assert(ex.lower_time() <= ex.upper_time())
            seqx = pre + [ex] + post
            seqsx.append(seqx)
        seqs = seqsx
      eventseqs += seqs

    # fix activity and data
    realizations = []
    for events in eventseqs:
      reals = [[]]
      for e in events:
        e.fix_time(e.lower_time())
        ers = e.get_realizations()
        reals = [ r + [er] for r in reals for er in ers ]
      realizations += reals
    return realizations

  def to_xes(self, doc):
    xtrace = doc.createElement('trace')
    for event in self._events:
      xevent = event.to_xes(doc)
      xtrace.appendChild(xevent)
    return xtrace


class UncertainLog:

  def __init__(self, traces):
    self._traces = traces

  def __str__(self):
    return "[" + ','.join([str(t) for t in self._traces]) + "]"

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
