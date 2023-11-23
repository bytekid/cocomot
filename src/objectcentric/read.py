import json

from objectcentric.input import Trace, Log, Event

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
    event = Event(int(id), act, time, objs)
    events.append(event)
    # FIXME what is ocel:vmap?
  objects = {}
  for (name, data) in content["ocel:objects"].items():
    objects[name] = data["ocel:type"]
  return Log(events, ordering, objects)

