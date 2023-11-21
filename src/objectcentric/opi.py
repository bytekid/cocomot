from sys import maxsize
import xml.dom.minidom
import itertools

from utils import VarType
from dpn.dpn import DPN

# object-centric petri nets with identifiers
class OPI(DPN):

  def __init__(self, opi_as_array):
    super().__init__(opi_as_array)

  def step_bound(self, trace):
    return 12 # len(trace) + self.shortest_accepted()

  #def object_bound(self, trace):
  #  return len(trace.get_objects())

  def add_silent_finals(self, map):
    id = len(map) + 1
    for p in self.final_places():
      insc = [a["inscription"] for a in self._arcs if a["target"] == p["id"]][0]
      t = {"id": id, "invisible": True, "label": "silent final"+str(id) }
      self._transitions.append(t)
      self._silent_final_transitions.append(t["id"])
      self._arcs.append({"source": p["id"], "target": id, "inscription": insc})
      self._arcs.append({"target": p["id"], "source": id, "inscription": insc})
      map[id] = t
      id += 1
      break

  def objects_by_type(self, trace, with_ids = True):
    # return for every type a list of tuples containing object name and id
    # (id is unique among all objects)
    objs = trace.get_objects()
    objs_by_type = dict([ (typ,[]) for typ in objs.values()])
    id = 0
    for (o,t) in objs.items():
      objs_by_type[t].append((o, id) if with_ids else o)
      id += 1
    return objs_by_type

  def tokens_by_color(self, trace):
    objs_by_type = self.objects_by_type(trace, with_ids = False)
    colors = set([ p["color"] for p in self._places ])
    tokens_by_color = {}
    for color in colors:
      prod = itertools.product(*[ objs_by_type[typ] for typ in color ])
      tokens_by_color[color] = list(prod)
    return tokens_by_color

  # compute maximum number of objects involved in a transition firing
  def get_max_objects_per_transition(self, trace):
    max_obj = 0
    for t in self._transitions:
      id = t["id"]
      inscs = []
      for a in [a for a in self._arcs if a["source"] == id or a["target"] ==id]:
        inscs += a["inscription"]
      obj_count = 0
      objs_by_type = self.objects_by_type(trace)
      for (name, typ) in set(inscs):
        if typ in objs_by_type: # simple inscription
          obj_count += 1
        else:
          typ = typ[0:typ.rfind(" LIST")] 
          obj_count += len(objs_by_type[typ])
      max_obj = max(max_obj, obj_count)
    print("maximum number of objects used by transition:", max_obj)
    return max_obj

  def object_inscriptions_of_transition(self, trans, trace):
    # returns tuples (index, name, needed, type, in, place)
    objs_by_type = self.objects_by_type(trace)
    arcs = [ a for a in self._arcs if a["target"] == trans["id"] or \
      a["source"] == trans["id"] ]
    params = []
    indices = {}
    for a in arcs:
      place, is_in = (a["source"], True) if a["target"] == trans["id"] else \
        (a["target"], False)
      for (oname, otype) in a["inscription"]:
        if "LIST" in otype:
          basetype = otype[0:otype.rfind(" LIST")]
          for i in range(0, len(objs_by_type[basetype])):
            xname = oname+str(i)
            if not xname in indices:
              indices[xname] = len(indices)
            index = indices[xname]
            params.append({"name":oname, "xname": xname, "needed":False, \
              "type":basetype, "incoming": is_in, "place": place,"index":index})
        else:
          if not oname in indices:
            indices[oname] = len(indices)
          index = indices[oname]
          params.append({"name":oname,"xname":oname,"needed":True,"type":otype,\
            "incoming": is_in, "place": place, "index": index})
    #print("INSCRIPTION", trans["label"], params)
    return params

  def object_params_of_transition(self, trans, trace):
    inscset = set([])
    params = []
    index = 0
    for p in self.object_inscriptions_of_transition(trans, trace):
      if p["name"] in inscset: # add every parameter only once
        continue
      params.append({"name":p["name"], "needed":p["needed"], "type":p["type"], \
        "index": p["index"] })
      inscset.add(p["name"])
    return params

  def nu_transitions(self):
    nutrans = []
    for t in self._transitions:
      aout = [a for a in self._arcs if a["source"] == t["id"]]
      nuinscs = [o for a in aout for (o,_) in a["inscription"] if "nu" in o]
      assert(len(nuinscs) <= 1)
      if len(nuinscs) != 0:
        nutrans.append(t)
    return nutrans

  def pre(self, trans):
    ids = [a["source"] for a in self._arcs if a["target"] == trans["id"]]
    return [ p for p in self._places if p["id"] in ids ]

  def post(self, trans):
    ids = [a["target"] for a in self._arcs if a["source"] == trans["id"]]
    return [ p for p in self._places if p["id"] in ids ]

  def post_trans(self, place):
    ids = [a["target"] for a in self._arcs if a["source"] == place["id"]]
    return [ t for t in self._transitions if t["id"] in ids ]

  def pre_trans(self, place):
    ids = [a["source"] for a in self._arcs if a["target"] == place["id"]]
    return [ t for t in self._transitions if t["id"] in ids ]
