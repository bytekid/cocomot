from functools import reduce 

class Event:
  def __init__(self, id, activity, time, objects, valuation):
    self._id = id
    self._activity = activity
    self._time = time
    self._objects = objects
    self._valuation = valuation

  def __eq__(self, other):
    return self._id == other._id

  def __hash__(self):
    return self._id

  def get_activity(self):
    return self._activity

  def get_objects(self):
    return self._objects

  def get_valuation(self):
    return self._valuation

  def get_id(self):
    return self._id

  def __str__(self):
    objs = reduce(lambda acc, e: acc + str(e) + ",", self._objects, "")
    if len(objs) > 0:
      objs = objs[0:-1] # cut last ,
    bstr = lambda b: b + " -> " + str(self._valuation[b]) + ","
    vals = reduce(lambda acc,b: "%s%s" % (acc, bstr(b)), self._valuation, "")
    if len(vals) > 0:
      vals = vals[0:-1] # cut last ,
    return "(%d: %s {%s} {%s})" % (self._id, self._activity, objs, vals)


class Trace:
  def __init__(self, events, ordering, objects):
    self._events = sorted(events, key=lambda e: e.get_id())
    self._ordering = ordering
    self._objects = set(objects)

  def get_objects(self):
    return self._objects

  def smallest_object(self):
    return sorted(list(self._objects))[0] if len(self._objects) > 0 else None

  def get_events(self):
    return self._events

  def get_ordering(self):
    return self._ordering

  def __len__(self):
    return len(self._events)

  def __getitem__(self, index):
    if not isinstance(index, int):
      raise Exception("Trace indexing supports only integer indices")
    return self._events[index]
    
  def union(self, other):
    #print(self._events)
    #print(other._events)
    events = list(set(self._events).union(set(other._events)))
    return Trace(events,self._ordering,set(self._objects.union(other._objects)))

  def add_object_types(self, objtypes):
    obj_dict = {}
    for o in self._objects:
      obj_dict[o] = objtypes[o]
    self._objects = obj_dict
  
  def __str__(self):
    return reduce(lambda acc, e: acc + str(e) + ",", self._events, "")

class Log:
  def __init__(self, events, ordering, objects):
    self._events = events
    self._ordering = ordering
    self._objects = objects

  def split_into_traces(self):
    trace_of_object = {}
    for e in self._events:
      trace = Trace([e], self._ordering, e.get_objects())
      for o in e.get_objects():
        if o in trace_of_object:
          trace = trace.union(trace_of_object[o])
      for o in trace.get_objects():
        trace_of_object[o] = trace
    
    #traces = []
    #for (o,trace) in trace_of_object.items():
    #  if any( o in atrace for atrace in traces):
    #    continue
    #  traces.append(trace)
    #return traces
    traces = set(trace_of_object.values())
    for trace in traces:
      trace.add_object_types(self._objects) # make dictionary with types
    return traces
      


