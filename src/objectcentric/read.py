import json

class Trace:
  def __init__(self, events, ordering, objects):
    self._events = events
    self._ordering = ordering
    self._objects = objects

  def objects(self):
    return self._objects

  def events(self):
    return self._events

  def ordering(self):
    return self._ordering

  def __len__(self):
    return len(self._events)


class Log:
  def __init__(self, events, ordering, objects):
    self._events = events
    self._ordering = ordering
    self._objects = objects

  def split_into_traces(self):
    pass # TODO


def ocel(jsonfile):
  file = open(jsonfile, "r")
  input = file.read()
  content = json.loads(input)
  file.close()

  types = content["ocel:global-log"]["ocel:object-types"]
  ordering = content["ocel:global-log"]["ocel:ordering"] # list containing timestamp or sth else
  events = []
  for (id, e) in content["ocel:events"].items():
    act = e["ocel:activity"]
    time = e["ocel:timestamp"]
    objs = e["ocel:omap"]
    event = {"activity": act, "timestamp": time, "objects": objs, "id": id}
    events.append(event)
    # FIXME what is ocel:vmap?
  objects = {}
  for (name, data) in content["ocel:objects"].items():
    objects[name] = data["ocel:type"]
  return Trace(events, ordering, objects) # FIXME

