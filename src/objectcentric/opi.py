from sys import maxsize
import xml.dom.minidom
import itertools

from utils import VarType
from dpn.dpn import DPN

# object-centric petri nets with identifiers
class OPI(DPN):

  def __init__(self, opi_as_array):
    super().__init__(opi_as_array)
    self._step_bound = None
    self._objects = None

  def step_bound(self, trace):
    if not self._step_bound:
      objs_silent = self.objects_created_by_silent_transitions()
      b = int(len(objs_silent)) + max(self.shortest_accepted(), len(trace))
      self._step_bound = b
      print("step bound:", b, "silent objs:", objs_silent)
    return self._step_bound

  # The following function is called in the super constructor.
  # it is used for the 1st way to deal with an unknown length of the model run,
  # adding a silent final transition that is executed an arbitrary number of
  # times. However, it seems to reduce the runtime to at least 20% if instead
  # the finality constraint in the last instant is replaced by a finality 
  # constraint that is a disjunction over all instants.
  # Thus this function does currently nothing.
  def add_silent_finals(self, map):
    pass
    '''
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
    '''

  def get_types(self, objs):
    place_types = [ t for p in  self._places for t in p["color"]]
    obj_types = [ t for (o,t) in objs.items() ]
    return set(place_types + obj_types)

  def objects_by_type(self, objs, with_ids = True):
    if self._objects and with_ids:
      return self._objects
    
    # return for every type a list of tuples containing object name and id
    # (id is unique among all objects)
    objs_by_type = dict([ (typ,[]) for typ in self.get_types(objs)])
    id = 0
    for (o,t) in objs.items():
      objs_by_type[t].append((o, id) if with_ids else o)
      id += 1
    if with_ids:
      self._objects = objs_by_type
    return objs_by_type

  def tokens_by_color(self, objs):
    objs_by_type = self.objects_by_type(objs, with_ids = False)
    colors = set([ p["color"] for p in self._places ])
    tokens_by_color = {}
    for color in colors:
      prod = itertools.product(*[ objs_by_type[typ] for typ in color ])
      tokens_by_color[color] = list(prod)
    return tokens_by_color

  # compute maximum number of objects involved in a transition firing
  def get_max_objects_per_transition(self, objs):
    max_obj = 0
    for t in self._transitions:
      id = t["id"]
      inscs = []
      for a in [a for a in self._arcs if a["source"] == id or a["target"] ==id]:
        inscs += a["inscription"]
      obj_count = 0
      objs_by_type = self.objects_by_type(objs)
      for (name, typ) in set(inscs):
        if typ in objs_by_type: # simple inscription
          obj_count += 1
        else:
          typ = typ[0:typ.rfind(" LIST")] 
          obj_count += len(objs_by_type[typ])
      max_obj = max(max_obj, obj_count)
    print("maximum number of objects used by transition:", max_obj)
    return max_obj

  def objects_created_by_silent_transitions(self):
    nus = [ t for t in self.nu_transitions() if t["invisible"] ]
    nuids =  [ t["id"] for t in nus ]
    pids = [a["target"] for id in nuids for a in self._arcs if a["source"]==id]
    types = [ t for p in self._places for t in p["color"] if p["id"] in pids ]
    return set([ o for t in types for o in self._objects[t]])

  def object_inscriptions_of_transition(self, trans, objs):
    # returns tuples (index, name, needed, type, in, place)
    objs_by_type = self.objects_by_type(objs)
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

  def object_params_of_transition(self, trans, objs):
    inscset = set([])
    params = []
    index = 0
    for p in self.object_inscriptions_of_transition(trans, objs):
      if p["xname"] in inscset: # add every parameter only once
        continue
      params.append({"name":p["name"], "needed":p["needed"], "type":p["type"], \
        "index": p["index"] })
      inscset.add(p["xname"])
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

  def compute_reachable(self, trace):
    num_steps = self.step_bound(trace)
    (src, tgt) = ("source", "target")
    transs = dict([ (t["id"], t) for t in self._transitions ])
    idists = dict([ (t["id"], t["idist"]) for t in self.transitions()])
    fdists = dict([ (t["id"], t["fdist"]) for t in self.transitions()])
    self._reachable = []

    ps = [ p["id"] for p in self._places if "initial" in p ]
    states = [ (set(ps),[]) ] # pairs of current marking and transition history
    reachable_markings = []
    for i in range(0, num_steps):
      statesx = []
      # everything reachable in i-1 steps is also reachable in i steps,
      # at least with enough objects
      # FIXME make more precise
      self._reachable.append([])
      remaining = num_steps - i
      for (marking, steps) in states:
        for t in self._transitions:
          tid = t["id"]
          pre_t = [ a[src] for a in self._arcs if a[tgt] == tid]
          post_t = [ a[tgt] for a in self._arcs if a[src] == tid]
          if not set(pre_t).issubset(marking):
            continue # this transition is not enabled, skip
          markingx = marking.difference(pre_t).union(post_t)
          if not markingx in reachable_markings:
            statesx.append((markingx, steps + [tid]))
          #print("add marking", markingx)
          if not transs[tid] in self._reachable[i]: # and fdists[tid] < remaining:
            self._reachable[i].append(transs[tid])
        reachable_markings.append(marking)
      states = statesx

    # postprocessing for symmetry breaking: 
    # require silent nu transitions to occur in beginning, i.e., exclude later
    nuids =  [ t["id"] for t in self.nu_transitions() if t["invisible"] ]
    for i in range(len(self.objects_created_by_silent_transitions()),num_steps):
      self._reachable[i] = [t for t in self._reachable[i] if t["id"] not in nuids ]
      #print("reachable in ", i)
      #print([ [ t["label"] for t in self._transitions if t["id"]==tr["id"] ] for tr in self._reachable[i] ])

  def reachable(self, i):
    return self._reachable[i]

  def reset(self):
    self._step_bound = None