from sys import maxsize
from smt.z3solver import Z3Solver
import xml.dom.minidom
from copy import deepcopy

from dpn.expr import top, Bool, Cmp, BinOp, BinCon, Var, Num
from utils import VarType

class DPN:

  def __init__(self, dpn_as_array):
    dpn_as_array, map = self.mk_ids_integer(dpn_as_array)
    self.net = dpn_as_array
    self._places = dpn_as_array["places"]
    self._transitions = dpn_as_array["transitions"]
    self._variables = dpn_as_array["variables"]
    self._arcs = dpn_as_array["arcs"]
    self.has1token = None
    self._is_one_bounded = None
    self._silent_final_transitions = []
    self.add_silent_finals(map)
    self.compute_shortest_paths()
  
  def places(self):
    return self._places
  
  def transitions(self):
    return self._transitions
  
  def arcs(self):
    return self._arcs
  
  def variables(self):
    return self._variables

  # replace ids of places and ransitions by unique integers
  def mk_ids_integer(self, dpn):
    id = 0
    str2int = {}
    int2plc = {}
    for p in dpn["places"]:
      n = p["id"]
      int2plc[id] = dict(p) 
      p["id"] = id
      str2int[n] = id
      id += 1
    for p in dpn["transitions"]:
      n = p["id"]
      int2plc[id] = dict(p)
      p["id"] = id
      str2int[n] = id
      id += 1
    for a in dpn["arcs"]:
      if a["source"] not in str2int or a["target"] not in str2int:
        kind, key = ("source", a["source"]) if a["source"] not in str2int \
          else ("target", a["target"])
        print("Input error: arc %s %s unknown" % (kind, key))
        exit(1)
      a["source"] = str2int[a["source"]]
      a["target"] = str2int[a["target"]]
    return dpn, int2plc

  def has_final_places(self):
    return len(self.final_places()) > 0

  ### add silent transition to one final place (without label and constraint)
  def add_silent_finals(self, map):
    id = len(map) + 1
    for p in self.final_places():
      t = {"id": id, "invisible": True, "label":None, "write":[] }
      self._transitions.append(t)
      self._silent_final_transitions.append(t["id"])
      self._arcs.append({"source": p["id"], "target": id})
      self._arcs.append({"target": p["id"], "source": id})
      map[id] = t
      id += 1
      break
  
  def replace_disjunctive_guards(self):
    ids = [p["id"] for p in self.places()] + [t["id"] for t in self.transitions()]
    self._nextid = max(ids) + 1 # next free id

    def add(t, g):
      tnew = {
        "id": self._nextid,
        "label": t["label"],
        "constraint": g,
        "write": t["write"],
        "idist": t["idist"],
        "fdist": t["fdist"]
      }
      if "invisible" in t:
        tnew["invisible"] = t["invisible"]
      self._transitions.append(tnew)
      self._arcs += [{"source": a["source"], "target": self._nextid} \
        for a in self._arcs if a["target"] == t["id"]]
      self._arcs += [{"target": a["target"], "source": self._nextid} \
        for a in self._arcs if a["source"] == t["id"]]
      self._nextid += 1
    
    def is_or(f):
      return isinstance(f, BinCon) and f.op == "||"

    def split(t, guard): # idx is transition index
      #print("split", guard)
      if is_or(guard.left):
        split(t, guard.left)
      else:
        add(t, guard.left)
        #print("add", guard.left)
      if is_or(guard.right):
        split(t, guard.right)
      else:
        add(t, guard.right)
        #print("add", guard.right)

    trans = deepcopy(self._transitions)
    to_delete = []
    for (i, t) in enumerate(trans):
      # FIXME do dnf(nnf(t["guard"]))
      if "constraint" in t and is_or(t["constraint"]):
        to_delete.append(t["id"]) #del self._transitions[i]
        split(t, t["constraint"])
        self._arcs  = [ a for a in self._arcs \
          if a["target"] != t["id"] and a["source"] != t["id"]]

    self._transitions=[t for t in self._transitions if t["id"] not in to_delete]

  def is_silent_final_transition(self, id):
    return id in self._silent_final_transitions
  
  def post(self, p):
    return set([ l["target"] for l in self._arcs if l["source"]  == p])

  def is_acyclic(self, pid):
    ps = [pid]
    visited = set(ps)
    (src, tgt) = ("source", "target")
    while len(ps) > 0:
      trans = [ l[tgt] for l in self._arcs if l[src] in ps ]
      psx = set([ l[tgt] for l in self._arcs if l[src] in trans])
      if pid in psx:
        return False
      elif psx.issubset(visited):
        return True
      ps = psx
      visited = visited.union(ps)
    return True

  # Parameter goals is a list of places.
  # Returns length of shortest path to some place in goals, starting from either
  # the initial places (if forward=True) or the final places (forward=False).
  def shortest_to(self, goals, forward = True):
    arcs = self._arcs
    (src, tgt) = ("source", "target") if forward else ("target", "source")
    def shortest(n, ns):
      if n["id"] in goals:
        return 0
      elif n in ns:
        return 1000 # no reachable goal state: the hack to infinity
      else:
        trans = [ l[tgt] for l in arcs if l[src] == n["id"] ]
        next_places = [ l[tgt] for l in arcs if l[src] in trans ]
        return 1 + min([shortest(places[p], [n]+ns) for p in next_places] +[1000])
    
    places = dict([ (p["id"], p) for p in self._places ])
    if forward:
      start = [p for p in places.values() if "initial" in p and p["initial"]]
    else:
      start = [p for p in places.values() if "final" in p and p["final"]]
    # if initial marking is empty, return 0
    return min([ shortest(p, []) for p in start ]) if len(start) > 0 else 0

  def final_places(self):
    return [ p for p in self._places if "final" in p and p["final"]]

  def shortest_accepted(self):
    finals = [ p["id"] for p in self._places if "final" in p and p["final"]]
    l = self.shortest_to(finals)
    return l if self.has_single_token() else 6 # FIXME

  # for every transition, compute the minimal distance to an initial/final place
  def compute_shortest_paths(self):
    for t in self._transitions:
      srcs = [ l["source"] for l in self._arcs if l["target"] == t["id"] ]
      t["idist"] = self.shortest_to(srcs) # min distance to initial
      tgts = [ l["target"] for l in self._arcs if l["source"] == t["id"] ]
      t["fdist"] = self.shortest_to(tgts, forward=False) # min distance to final

  # assumes one-boundedness
  def simulate_markings(self, num_steps):
    (src, tgt) = ("source", "target")
    transs = dict([ (t["id"], t) for t in self._transitions ])
    idists = dict([ (t["id"], t["idist"]) for t in self.transitions()])
    fdists = dict([ (t["id"], t["fdist"]) for t in self.transitions()])

    ps = [ p["id"] for p in self._places if "initial" in p ]
    states = [ (set(ps),[]) ] # pairs of current marking and transition history
    seen_acylic = set([])
    is_one_bounded = True
    for i in range(0, num_steps):
      if i > 12 or len(states) > 22: # gets too expensive, do approximation
        ts = [ t for (id, t) in transs.items() if fdists[id] < rem and i >= idists[id] ]
        seen_acylic_sub = [tid for tid in seen_acylic if tid not in [t["id"] for t in self._reachable[i-1]]]
        ts_sub = [t for t in ts if not t["id"] in seen_acylic_sub]
        self._reachable.append(ts_sub)
        is_one_bounded = False # too expensive
      else:
        statesx = []
        self._reachable.append([])
        rem = num_steps - i
        for (marking, steps) in states:
          for t in self._transitions:
            tid = t["id"]
            pre_t = [ a[src] for a in self._arcs if a[tgt] == tid]
            post_t = [ a[tgt] for a in self._arcs if a[src] == tid]
            if not set(pre_t).issubset(marking):
              continue # this transition is not enabled, skip
            m = list(marking.difference(pre_t)) + post_t
            markingx = marking.difference(pre_t).union(post_t)
            if len(marking) != len(markingx):
              is_one_bounded = False
            statesx.append((markingx, steps + [tid]))
            if not transs[tid] in self._reachable[i] and fdists[tid] < rem:
              self._reachable[i].append(transs[tid])
              if self.is_acyclic(tid):
                seen_acylic = seen_acylic.union({tid})
      states = statesx
      self._is_one_bounded = is_one_bounded


  def compute_reachable(self, num_steps):
    self._reachable = []
    
    if self.has_single_token():
      fdists = dict([ (t["id"], t["fdist"]) for t in self.transitions()])
      transs = dict([ (t["id"], t) for t in self._transitions ])
      pids = [ t["id"] for t in self._places ]
      
      (src, tgt) = ("source", "target")
      ps = [ p["id"] for p in self._places if "initial" in p ]
      for i in range(0, num_steps):
        rem = num_steps - i
        ts = [ l[tgt] for l in self._arcs if l[src] in ps ]
        self._reachable.append([transs[t] for t in set(ts) if fdists[t] < rem])
        ps = set([ a[tgt] for a in self._arcs if a[src] in ts])
    else:
      self.simulate_markings(num_steps)
      
  
  # set of transitions reachable within i steps
  def reachable(self, i):
    return self._reachable[i]
  
  # compute minimal number of steps needed before variable is written
  def var_write_reach(self):
    vreach = []
    for i in range(0,len(self._reachable)):
      vs = [v for t in self._reachable[i] if "write" in t for v in t["write"]]
      vreach.append(list(set(vs)))
    return vreach
      
  
  # transitions reachable from transition t in >= 1 step, overapproximation
  def reachable_from_trans(self, tstart_id):
    (src, tgt) = ("source", "target")
    post_t = [ a[tgt] for a in self._arcs if a[src] == tstart_id]
    frontier = set([ a[tgt] for a in self._arcs if a[src] in post_t ])
    reachable = frontier
    while len(frontier) > 0:
      nextfrontier = set([])
      for tid in frontier:
        post_t = [ a[tgt] for a in self._arcs if a[src] == tid]
        next = set([ a[tgt] for a in self._arcs if a[src] in post_t ])
        nextfrontier = nextfrontier.union(next)
      frontier = nextfrontier.difference(reachable)
      reachable = reachable.union(nextfrontier)
    return reachable

  def single_occurrence_transitions(self):
    transs = dict([ (t["id"], t) for t in self._transitions ])
    ts = [ t["id"] for t in self._transitions \
      if not t["invisible"] \
      if all(t["label"] != transs[t2]["label"] for t2 in self.reachable_from_trans(t["id"]))]
    return set(ts)

  def directly_follows_transitions(self):
    if self.has1token:
      return []
    pairs = []
    for t in self._transitions:
      post_t = [ a["target"] for a in self._arcs if a["source"] == t["id"]]
      tnexts = [ a["target"] for a in self._arcs if a["source"] in post_t ]
      if len(tnexts) == 1:
        pairs.append(tuple([t["id"], tnexts[0]]))
    return pairs

  def is_one_bounded(self):
    if self.has1token:
      return True
    if self._is_one_bounded != None:
      return self._is_one_bounded
    self.simulate_markings()
    return self._is_one_bounded

  def has_single_token(self):
    if self.has1token != None:
      return self.has1token
    
    for p in self.places():
      if "initial" in p and p["initial"] > 1:
        self.has1token = False
        return False
        
    for t in self._transitions:
      outs = [ a for a in self._arcs if a["source"] == t["id"]]
      ins = [ a for a in self._arcs if a["target"] == t["id"]]
      if len(outs) != len(ins):
        self.has1token = False
        return False
    self.has1token = True
    return True

  def lower_bound_alignment_cost(self, trace):
    events = [e["label"] for e in trace]
    # multiple occurrences of transitions that can occur only once in model runs
    singles = set([ t["label"] for tid in self.single_occurrence_transitions() \
      for t in self.transitions() if t["id"] == tid])
    d = [len([ e for e in trace if e['label'] == l]) for l in singles]
    bnd = max(d+[1]) - 1
    #print("initial", d, bnd)

    cmps=set([])
    solver = Z3Solver()
    subst = {}
    for v in self.variables():
      if v["type"] not in ["java.lang.String", "java.lang.Boolean"]:
        vals = [e["valuation"][v["name"]] for e in trace if v["name"] in e["valuation"]]
        if len(vals) == 1:
          subst[v["name"]] = solver.real(vals[0])
          subst[v["name"]+"'"] = solver.real(vals[0])
    relevant_transs = [t for t in self._transitions if not "invisible" in t and \
      t["label"] in events]
    for t in relevant_transs:
      if "constraint" in t:
        for cmp in t["constraint"].comparisons():
          cmpsmt = cmp.toSMT(solver, subst)
          if solver.simplify(cmpsmt) == solver.false():
            bnd += 1
            #print(t["label"],t["constraint"], cmpsmt, "not sat")

    solver.destroy()
    return bnd

  def hackstates(self, k):
    #print("<!-- hack states", k, "-->")

    thesource = self._places[2]["id"] # a place
    thetarget = [ a["target"] for a in self._arcs if a["source"] == thesource][0]
    trans = [t for t in self._transitions if not t["id"] in self._silent_final_transitions ]
    arcs = [a for a in self._arcs if not (a["source"] == thesource and a["target"] == thetarget) and \
      not (a["source"] in self._silent_final_transitions or a["target"] in self._silent_final_transitions) ]
    
    places = dict([(p["id"], p) for p in self._places])
    lastid = thesource
    for i in range(0, k):
      l = len(places)
      assert(not(l in places))
      places[l] = {"id": "p"+str(l), "name": "pdummy" + str(l) }
      trans.append({"id": "t"+str(l), "label": "Inv_" + str(l), "invisible":True })
      arcs.append({"id": "1"+str(len(arcs)), "source": lastid, "target": "t"+str(l), \
        "name":"arcdummy1"+str(i), "constraint":top, "written":[]})
      arcs.append({"id": "2"+str(len(trans)), "source": "t"+str(l), "target": "p"+str(l), \
        "name":"arcdummy2"+str(i), "constraint":top, "written":[]})
      lastid = "p"+str(l)

    arcs.append({"id": len(trans), "source": lastid, "target": thetarget, \
      "name":"tdummy"+str(k), "constraint":top, "written":[]})

    for t in trans:
      if "constraint" in t:
        t["constraint"] = str(t["constraint"]) 

    vars = []
    for v in self._variables:
      #v["type"] = "bool" if v["type"] == "bool" else VarType.to_str(v["type"])
      vars.append(v)

    dpn = {
      "places": list(places.values()) , 
      "transitions": trans,
      "arcs":arcs,
      "variables": vars}
    return DPN(dpn)

  def expand(self, k, g):
    if k == 0:
      return g

    vars = dict([(v["name"], v) for v in self._variables])

    def expand_cmp(c):
      if not isinstance(c.left, Var): # and not isinstance(c.right, Var):
        #print("do not change", c)
        return (c, [])
      v = str(c.left)
      is_written = v[-1] == "'"
      #print(c, is_written)
      vbase = v if not is_written else v[0:-1]
      t = vars[vbase]["type"]
      var = lambda i: Var(vbase + str(i), True if is_written else None, type=t)
      e = Cmp("==", c.left, var(0))
      for i in range(1, k):
        e = BinCon(e, "&&", Cmp("==", var(i-1), var(i)))
      return BinCon(e, "&&", Cmp(c.op, var(k-1), c.right))
    
    if isinstance(g, BinCon):
      c = self.expand(k, g.left)
      return BinCon(c, g.op, g.right)
    elif isinstance(g, Cmp):
      return expand_cmp(g)
    elif isinstance(g, Bool):
      return g
    print(g)
    assert(False)
  
  def hackvars(self, k):
    vars = deepcopy(self._variables)
    trans = deepcopy(self._transitions)

    for v in self._variables:
      type = v["type"]
      name = v["name"]
      for i in range(0, k):
        vars.append({"name":name + str(i), "type":type, "initialValue":0 if type != "java.lang.Bool" else False})

    for t in trans:
      if "constraint" in t:
        #print("before", t["constraint"])
        g = self.expand(k, t["constraint"])
        #print("after", g, "\n")
        #print("written", ws)
        t["constraint"] = str(g)
      ws = [ v+str(i) for v in t["write"] for i in range(0,k)]
      t["write"] = t["write"] + ws if "write" in t else ws
    
    dpn = {
      "places": self._places, 
      "transitions": trans,
      "arcs":self._arcs,
      "variables": vars}
    return DPN(dpn)
       

  def export_pnml(self):
    doc = xml.dom.minidom.parseString("<pnml/>")

    def place_to_pnml(p):
      xplace = doc.createElement("place")
      xplace.setAttribute("id", str(p["id"]))
      xname = doc.createElement("name")
      xplace.appendChild(xname)
      xtext = doc.createElement("text")
      xname.appendChild(xtext)
      xlabel = doc.createTextNode(str(p["id"]))
      xtext.appendChild(xlabel)
      xplace.appendChild(xname)
      if "initial" in p:
        ximark = doc.createElement("initialMarking")
        xtext = doc.createElement("text")
        ximark.appendChild(xtext)
        xlabel = doc.createTextNode("1")
        xtext.appendChild(xlabel)
        xplace.appendChild(ximark)
      if "final" in p:
        xfmark = doc.createElement("finalMarking")
        xtext = doc.createElement("text")
        xfmark.appendChild(xtext)
        xlabel = doc.createTextNode("1")
        xtext.appendChild(xlabel)
        xplace.appendChild(xfmark)
      return xplace

    def trans_to_pnml(p):
      xtrans = doc.createElement("transition")
      xtrans.setAttribute("id", str(p["id"]))
      xname = doc.createElement("name")
      xtrans.appendChild(xname)
      xtext = doc.createElement("text")
      xname.appendChild(xtext)
      xlabel = doc.createTextNode(str(p["label"]))
      xtext.appendChild(xlabel)
      if "write" in p:
        for v in p["write"]:
          xwrite = doc.createElement("writeVariable")
          xtext = doc.createTextNode(v)
          xwrite.appendChild(xtext)
          xtrans.appendChild(xwrite)
      if "invisible" in p and p["invisible"]:
        xtrans.setAttribute("invisible", "true")
      if "constraint" in p:
        xtrans.setAttribute("guard", p["constraint"])
      return xtrans

    def arc_to_pnml(a):
      xarc = doc.createElement("arc")
      xarc.setAttribute("source", str(a["source"]))
      xarc.setAttribute("target", str(a["target"]))
      if "id" in a:
        xarc.setAttribute("id", str(a["id"]))
      return xarc
      
    def var_to_pnml(v):
      xvar = doc.createElement("variable")
      xvar.setAttribute("maxValue", "1000000")
      xvar.setAttribute("minValue", "0")
      xname = doc.createElement("name")
      xvar.appendChild(xname)
      xtext = doc.createTextNode(v["name"])
      xname.appendChild(xtext)
      xvar.setAttribute("type", v["type"])
      return xvar


    root = doc.documentElement
    xnet = doc.createElement("net")
    xnet.setAttribute("id", "net1")
    xnet.setAttribute("type", "http://www.pnml.org/version-2009/grammar/pnmlcoremodel")
    root.appendChild(xnet)
    xpage = doc.createElement("page")
    xpage.setAttribute("id", "page1")
    xnet.appendChild(xpage)

    for p in self._places:
      xpage.appendChild(place_to_pnml(p))
    for t in self._transitions:
      xpage.appendChild(trans_to_pnml(t))
    for a in self._arcs:
      xpage.appendChild(arc_to_pnml(a))
    xvars = doc.createElement("variables")
    xnet.appendChild(xvars)
    for v in self._variables:
      xvars.appendChild(var_to_pnml(v))
    return root
    