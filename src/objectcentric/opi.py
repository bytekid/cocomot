from sys import maxsize
import xml.dom.minidom
import itertools

from utils import VarType
from dpn.dpn import DPN

# object-centric petri nets with identifiers
class OPI(DPN):

  def __init__(self, opi_as_array):
    super().__init__(opi_as_array)
    for p in self._places:
      p["color"] = tuple(p["color"].split(","))

  def step_bound(self, trace):
    return len(trace) + self.shortest_accepted()

  #def object_bound(self, trace):
  #  return len(trace.get_objects())

  def add_silent_finals(self, map):
    id = len(map) + 1
    for p in self.final_places():
      insc = [a["inscription"] for a in self._arcs if a["target"] == p["id"]][0]
      t = {"id": id, "invisible": True, "label": None }
      self._transitions.append(t)
      self._silent_final_transitions.append(t["id"])
      self._arcs.append({"source": p["id"], "target": id, "inscription": insc})
      self._arcs.append({"target": p["id"], "source": id, "inscription": insc})
      map[id] = t
      id += 1
      break

  def objects_by_type(self, trace):
    # return for every type a list of tuples containing object name and id
    # (id is unique among all objects)
    objs = trace.get_objects()
    objs_by_type = dict([ (typ,[]) for typ in objs.values()])
    id = 0
    for (o,t) in objs.items():
      objs_by_type[t].append((o, id))
      id += 1
    return objs_by_type

  def tokens_by_color(self, trace):
    objs_by_type = self.objects_by_type(trace)
    colors = set([ p["color"] for p in self._places ])
    tokens_by_color = {}
    for color in colors:
      prod = itertools.product(*[objs_by_type[typ][0] for typ in color])
      tokens_by_color[color] = list(prod)
    #print(tokens_by_color)
    return tokens_by_color

  # compute maximum number of objects involved in a transition firing
  def get_max_objects_per_transition(self, trace):
    max_obj = 0
    for t in self._transitions:
      id = t["id"]
      inscs = []
      for a in [a for a in self._arcs if a["source"] == id or a["target"] ==id]:
        inscs += a["inscription"].split(",")
      obj_count = 0
      objs_by_type = self.objects_by_type(trace)
      for insc in set(inscs):
        typ = insc[insc.find(":")+1:]
        if typ in objs_by_type: # simple inscription
          obj_count += 1
        else:
          typ = typ[0:typ.rfind(" LIST")] 
          obj_count += len(objs_by_type[typ])
      max_obj = max(max_obj, obj_count)
    print("maximum number of objects used by transition:", max_obj)
    return max_obj

  def object_params_of_transition(self, trans, trace):
    # returns tuples (name, indexed_name, needed, type)
    objs_by_type = self.objects_by_type(trace)
    inarcs = [ a for a in self._arcs if a["target"] == trans["id"]]
    inscset = set([])
    tobjects = []
    for a in inarcs:
      for o in a["inscription"].split(","):
        oname = o[0:o.rfind(":")]
        otype = o[o.rfind(":")+1:]
        if oname in inscset:
          continue
        if "LIST" in otype:
          basetype = otype[0:otype.rfind(" LIST")]
          for i in range(0, len(objs_by_type[basetype])):
            tobjects.append((oname, oname+str(i), False, basetype))
        else:
          tobjects.append((oname, oname, True, otype))
        inscset.add(oname)
    return tobjects