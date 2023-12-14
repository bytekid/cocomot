from xml.dom.minidom import getDOMImplementation
import xml.dom.minidom
from datetime import datetime, timedelta
import sys
from random import random, sample, randint, seed
import time
from copy import deepcopy

from smt.z3solver import Z3Solver
from smt.ysolver import YicesSolver
from dpn.expr import top, Bool, Cmp, BinOp, BinCon, Var, Num
from utils import VarType
from encoding.encoding import Encoding
from cluster.intervals import *
from utils import pad_to, spaces

kinds = {
  "java.lang.Boolean": "bool",
  "java.lang.Integer": "int",
  "java.lang.Long": "int",
  "java.lang.Double": "float",
  "java.lang.String": "string"
}

def print_sequence(dpn, seq, tab = 12):
  transs = dict([ (t["id"], t) for t in dpn.transitions() ])
  a = spaces(tab+1)
  # print transition label sequence (or >> for skip step)
  for i in range(0, len(seq)):
    a += pad_to(seq[i]["label"], tab) + " " if seq[i] else "  >>"+spaces(tab-3)
  print(a)
  # print valuation sequence for each variable
  for v in dpn.variables():
    name = v["name"]
    a = pad_to(name, tab) + " "
    for i in range(0, len(seq)):
      if seq[i] == None: # is a skip step >>
        a += spaces(tab+1)
        continue

      val = seq[i]["valuation"]
      j = i - 1 # search last valuation
      while j > 0 and seq[j] == None:
        j -= 1
      val_pre = seq[j]["valuation"] if j >= 0 and  seq[j] != None else {}
      if "id" in seq[i]:
        trans = transs[seq[i]["id"]]
        v_written = "write" in trans and name in trans["write"]
      else:
        v_written = False
      change = (i==0 or (name not in val_pre) or (val[name]!=val_pre[name])) or\
        v_written if name in val else None
      if (name in val or i == 0) and change:
        if "String" in v["type"]:
          value = Expr.strval(val[name]) if name in val else ""
        else:
          value = val[name] if name in val else 0
        a += pad_to(str(value), tab) + " "
      else:
        a += spaces(tab+1)
    print(a)


def print_trace_distance_verbose(dpn, trace, decoding):
  places = dict([ (p["id"], p) for p in dpn.places() ])
  transs = dict([ (p["id"], p) for p in dpn.transitions() ])
  valuations = []
  run = decoding["run"]
  #print("\nMARKING:")
  #for i in range(0, len(run["markings"])):
  #  marking = ""
  #  for (p,count) in list(run["markings"][i].items()):
  #    for c in range(0, count):
  #      marking = marking + (" " if marking else "") + str(places[p]["name"])
  #  print("  %d: %s" % (i, marking))

  # shift model and log sequences to account for >> in alignment
  modelseq = []
  idx = 0
  alignment = decoding["alignment"]
  for i in range(0, len(alignment)):
    if alignment[i] in ["model", "parallel"]:
      (tid, tlab) = run["transitions"][idx]
      if tlab != "tau": # FIXME needed?
        val = run["valuations"][idx + 1]
        step = { "id": tid, "label": tlab, "valuation": val }
        modelseq.append(step)
      idx += 1
    else:
      if alignment[i] == "log":
        modelseq.append(None)
  traceseq = []
  idx = 0
  for i in range(0, len(alignment)):
    if alignment[i] in ["log", "parallel"]:
      traceseq.append(trace[idx])
      idx += 1
    elif alignment[i] == "model":
      traceseq.append(None)

  print("LOG SEQUENCE:")
  print_sequence(dpn, traceseq)
  print("\nMODEL SEQUENCE:")
  print_sequence(dpn, modelseq)
  sys.stdout.flush()

class Playout:
  def __init__(self, dpn):
    self._dpn = dpn
    dpn.replace_disjunctive_guards()
    self._solver = YicesSolver()

  def blur_trace(self, trace, activities, p):
    for e in trace._events:
      if random() <= p: # change sth
        kind = randint(0, len(e._data.keys()))
        if kind == 0:
          e._act = activities[randint(0, len(activities)-1)]
        else:
          var = list(e._data.keys())[kind-1]
          r = randint(-100, 100)
          (k, val) = e._data[var]
          if k == "float":
            r = r + float(randint(0, 100))/100
          e._data[var] = (k, val + r)
    if random() <= p:
      idx = randint(0, len(trace))
      trace._events.insert(idx, trace._events[randint(0, len(trace)-1)])


  def blur_traces(self, traces,  p):
    activities = list(set([ e._activity for t in traces for e in t._events ]))
    for t in traces:
      self.blur_trace(t, activities, p)


  def create_trace(self, transitions, encoding, model):
    #print("generate trace")
    events = []
    trace = []
    time = datetime.strptime("2021-01-01T00:00:00", "%Y-%m-%dT%H:%M:%S")
    vs = dict([ (v["name"], v) for v in self._dpn.variables() ])
    dvars = encoding._vs_data
    for (i,t) in enumerate(transitions):
      if "invisible" in t and t["invisible"]:
        continue
      val = {}
      if "write" in t:
        for v in t["write"]:
          if kinds[vs[v]["type"]] == "float":
            value = model.eval_real(dvars[i+1][v])
          else:
            value = model.eval_int(dvars[i+1][v])
          val[v] = (kinds[vs[v]["type"]], value)
      trace.append(Event(t["label"], time, val))

      time = time + timedelta(days=1)
    return TraceAbstraction(trace)


  def create_trace_abstractions(self, transitions):
    #print("generate trace")
    #for t in transitions:
    #  print("  ", t["label"], t["constraint"] if "constraint" in t else "")
    events = []
    time = datetime.strptime("2021-01-01T00:00:00", "%Y-%m-%dT%H:%M:%S")
    vs = [v["name"] for v in self._dpn.variables()]
    # mapping variable names to intervals of possible values. None=unrestricted
    vs_intervals = dict([((v,i), None) for v in vs \
      for i in range(0,len(transitions))])

    # loop to determine valuations
    for (i,t) in enumerate(transitions):
      # reset intervals for written variables
      if "write" in t:
        for v in t["write"]:
          vs_intervals[(v,i)] = None
      # first copy the prev valuation
      if i > 0:
        for v in vs:
          vs_intervals[(v,i)] = vs_intervals[(v,i-1)]
      # update intervals according to constraint
      if "constraint" in t:
        assert( not (isinstance(t["constraint"], BinCon) and t["constraint"].op == "||"))
        cmps = t["constraint"].comparisons()
        assert(all( is_interval_cmp(c) for c in cmps))
        cmp_ivals = [ ival for c in cmps for ival in cmp_intervals(c) ]
        for (v, ival) in cmp_ivals:
          if not vs_intervals[(v,i)]:
            vs_intervals[(v,i)] = set([ival])
          else:
            #print("interset ", ival, "and")
            #for iv in vs_intervals[(v,i)]:
            #  print(" ", iv)
            vs_intervals[(v,i)] = intersect_all(ival, vs_intervals[(v,i)])
            #print("result")
            #for iv in vs_intervals[(v,i)]:
            #  print(" ", iv)
          s = ""
          for iv in  vs_intervals[(v,i)]:
            s = s + " " + str(iv)
          #print(" update to", s)
          # propagate back FIXME would be nicer with mutble thingy being updated
          j = i-1
          while (j >= 0 and v not in transitions[j+1]["write"]):
            vs_intervals[(v,j)] = vs_intervals[(v,i)]
            #print("  propagate to ", j)
            j -= 1
      
    # loop to create trace
    for (i,t) in enumerate(transitions):
      if "invisible" in t and t["invisible"]:
        continue

      activity = t["label"]
      valuation = {}
      for v in [v for v in self._dpn.variables() if v["name"] in t["write"]]:
        vname = v["name"]
        kind = kinds[v["type"]]
        ival = vs_intervals[(vname,i)]
        valuation[vname] = (kind, list(ival) if ival else None)
      events.append( (activity, time, valuation) )

      time = time + timedelta(days=1)

    return self.all_trace_combinations(events)

  def all_trace_combinations(self, events):
    def to_val_dict(vals):
      return dict([ (x, (k,v)) for (x, k, v) in vals])

    traces = [[]]
    for (act,tim,valpattern) in events:
      # create set of possible interval valuations
      vals = [[]]
      for (x, (k, ivals)) in valpattern.items():
        if ivals: # not None, i.e., at least one interval
          vals = [ val + [(x,k,ival)] for val in vals for ival in ivals]
        else:
          vals = [ val + [(x,k,None)] for val in vals]
      traces = [ t + [Event(act, tim, to_val_dict(val))] \
        for t in traces for val in vals ]
    ts = [TraceAbstraction(t) for t in traces]
    #for t in ts:
    #  print(t)
    return ts


  # generate a set of traces L of length at most max_length, such that L contains
  # all control-flow sequences with some admissible data (if such data values
  # exist)
  def generate(self, max_length):
    dpn = self._dpn
    s = self._solver
    places = dpn.places()
    transitions = dpn.transitions()
    finals = [p["id"] for p in places if "final" in p and p["final"]]
    inits = [p["id"] for p in places if "initial" in p and p["initial"]]

    dpn.compute_reachable(max_length)
    enc = Encoding(dpn, s, max_length)
    self._encoding = enc

    def pre(t):
      return [a["source"] for a in dpn._arcs if a["target"] == t]

    def post(t):
      return [a["target"] for a in dpn._arcs if a["source"] == t]

    def enabled(t, marking):
      return len(pre(t)) > 0 and all(p in marking for p in pre(t))

    frontier = [ (set([p for p in inits]), [], s.true())]
    abstracttraces = []
    realtraces = []

    while len(frontier) > 0:
      frontier_new = []
      for (m, path, constr) in frontier:
        # print(m, path)
        k = len(path)
        for t in [ t for t in transitions if enabled(t["id"], m) ]:
          # print("do " + (t["label"] if "label" in t and t["label"] else "?"))
          m_new = m.difference(pre(t["id"])).union(post(t["id"]))
          path_new = path + [t]
          constr_new  = s.land([constr, enc.data_constraints(t, k)])
          model = s.check_sat(constr_new)
          if not model:
            # print("unsatisfiable path", constr_new)
            continue
          if set(m_new) == set(finals):
            newabstract = self.create_trace_abstractions(path)
            abstracttraces += newabstract
            newtrace = self.create_trace(path, enc, model)
            for a in newabstract:
              if self.trace_matches(a, newtrace):
                match = a
                break
            #print("should match")
            #print(newtrace)
            #for a in newabstract:
            #  print(" ", a)
            realtraces.append( (newtrace, match) )
          model.destroy()
          if len(path_new) < max_length:
            frontier_new.append( (m_new, path_new, constr_new) )
      frontier = frontier_new

    # make traces unique
    sts = [ (i, str(t), t) for (i,t) in enumerate(abstracttraces)]
    utraces = [ t for (i,s,t) in sts \
      if all( s != s2 for (i2,s2,t2) in sts if i2 > i) ]
    return utraces, realtraces

  def trace_matches(self, abstract, real):
    if len(abstract) != len(real):
      return False
    for i in range(0, len(real)):
      ae = abstract[i]
      re = real[i]
      if ae._activity != re._activity:
        return False
      assert(set(ae._data.keys()) == set(re._data.keys()))
      for x in re._data.keys():
        ival = ae._data[x][1]
        if (ival != None) and not ival.mem(re._data[x][1]):
          return False
    return True


  def adapt_trace(self, trace):
    def data(d):
      return dict([ (v, x) for (v, (_, x)) in d.items() ])
    return [ {"label": e._activity, "valuation": data(e._data) } \
      for e in trace._events]

  def get_model_run(self, model):
    encoding = self._encoding
    trans = dict([ (t["id"], t) for t in self._dpn._transitions ])
    run_length_dec = encoding.decode_run_length(model)
    (_, transitions, valuations) = encoding.decode_process_run(model, run_length_dec)
    vs = dict([ (v["name"], v) for v in self._dpn.variables() ])
    events = []
    time = datetime.strptime("2021-01-01T00:00:00", "%Y-%m-%dT%H:%M:%S")
    for (i,t) in enumerate(transitions):
      (id, label) = t
      if trans[id]["invisible"]:
        continue
      val = dict([ (n, (kinds[vs[n]["type"]], v)) \
        for (n, v) in valuations[i+1].items() if n in trans[id]["write"]])
      events.append(Event(label, time, val))
      time = time + timedelta(days=1)
    return TraceAbstraction(events)

  def conformance_check(self, trace):
    #print(trace)
    encoding = self._encoding
    solver = self._solver

    trace = self.adapt_trace(trace)

    solver.push()
    t_start = time.perf_counter()
    f_initial = encoding.initial_state()
    f_trans_range = encoding.transition_range()
    f_tokens = encoding.transition_constraints()
    f_final = encoding.final_state()
    encoding.prepare_edit_distance(len(trace))
    solver.require([f_initial, f_trans_range, f_tokens, f_final])
    (dist, dconstr) = encoding.edit_distance(trace)
    encoding.solver().require([dconstr])
    model = encoding.solver().minimize(dist, encoding.step_bound()+4)
    t_check = time.perf_counter() - t_start

    distance = model.eval_int(dist)
    print(distance)
    sys.stdout.flush()
    #alignment_decoded = encoding.decode_alignment(trace, model)
    #print_trace_distance_verbose(self._dpn, trace, alignment_decoded)
    model_run = self.get_model_run(model)
    model.destroy()
    solver.pop()
    solver.reset()
    return (model_run, distance, t_check)

  def adjust_values(self, realtrace, abstracttrace):
    for i in range (0, len(realtrace)):
      if not(len(realtrace) == len(abstracttrace)):
        continue
      for v in abstracttrace[i]._data.keys():
        (k, ival) = abstracttrace[i]._data[v]
        if not ival:
          realtrace[i]._data[v] = (k, randint(0, 1000))
        else:
          realtrace[i]._data[v] = (k, ival.random())

  def generate_test_set(self, max_length, log, p = 0.2):
    abstracttraces, realtraces = self.generate(max_length)
    print("number of abstract traces", len(abstracttraces))
    for (t, ta) in realtraces:
      self.adjust_values(t, ta)
    
    if p == 0:
      return abstracttraces, realtraces

    realtraces1 = [ t for (t, _) in realtraces ]
    realtraces = []
    repeat = 1
    for i in range(0, repeat):
      realtraces += deepcopy(realtraces1)
      
    
    self.blur_traces(realtraces,p)
    
    
    logtraces = []
    vs = dict([ (v["name"], v) for v in self._dpn.variables() ])
    for t in log:
      if len(t) > max_length:
        continue
      tt = []
      for e in t:
        val = {}
        for v in e["valuation"]:
          val[v] = (kinds[vs[v]["type"]], e["valuation"][v])
        tt.append(Event(e["label"], None, val))
      logtraces.append(TraceAbstraction(tt))
    


    realtracesmatched = []
    total_time = 0
    distances = []
    hashes = set([])
    for t in logtraces: #realtraces:
      strt = str(t)
      if strt in hashes:
        continue
      hashes.add(strt)

      modelrun, d, time = self.conformance_check(t)
      distances.append(d)
      total_time += time
      for a in abstracttraces:
        if self.trace_matches(a, modelrun):
          # print(a)
          abstr = a
          break
      realtracesmatched.append( (t, abstr) )
    print("conformance checking time", total_time, " avg distance", float(sum(distances))/len(distances))
    print("num abstract", len(abstracttraces), len(set([ str(t) for t in abstracttraces])))
    print("num real", len(realtracesmatched), len(set([ str(t) for t in realtracesmatched])))
    return abstracttraces, realtracesmatched


class Event:
  def __init__(self, activity, time, data):
    self._activity = activity
    self._time = time
    self._data = data

  def __str__(self):
    s = ""
    for (d, (_, v)) in self._data.items():
      s += " " + d + ":" + str(v) + ","
    return "<%s, %s, [%s]>" % (self._activity, str(self._time), s)

  def activity_to_xes(self, doc):
    xstr = doc.createElement("string")
    xstr.setAttribute("key", "concept:name");
    xstr.setAttribute("value", self._activity);
    return xstr

  def time_to_xes(self, doc):
    xtime = doc.createElement("date")
    xtime.setAttribute("key", "time:timestamp")
    timeformat = "%Y-%m-%dT%H:%M:%S%z"
    xtime.setAttribute("value", self._time.strftime(timeformat) )
    return xtime

  def data_value_to_xes(self, doc, name, dval):
    (kind, interval) = dval
    if interval != None and not isinstance(interval, Interval):
      low = interval
      high = interval
      (lo, ho) = (False,False)
      #val = interval
      #xval = doc.createElement(kind)
      #xval.setAttribute("key", name)
      #xval.setAttribute("value", str(val))
      #return [xval]
    elif not interval: # unrestricted
      low = - sys.maxsize-1
      high = sys.maxsize
      (lo, ho) = (True,True)
    else:
      low, high = interval.low, interval.high
      (lo, ho) = (interval.low_open, interval.high_open)
    xval_low = doc.createElement(kind)
    xval_low.setAttribute("key", name+":low")
    xval_high = doc.createElement(kind)
    xval_high.setAttribute("key", name+":high")
    if kind == "string": # or name == "dismissal":
      pass
    elif kind == "boolean":
      low = "true" if low else "false"
      high = "true" if high else "false"
    else:
      low = low if kind == "float" else int(low)
      high = high if kind == "float" else int(high)
    xval_low.setAttribute("value", "%.2f" % (low))
    xval_high.setAttribute("value", "%.2f" % (high))
    xval_low.setAttribute("included","false" if lo else "true")
    xval_high.setAttribute("included","false" if ho else "true")
    return [xval_low, xval_high]

  def data_value_to_xes2(self, doc, name, dval):
    (kind, interval) = dval
    value = 0 if interval == None else \
      interval if not isinstance(interval, Interval) else \
      interval.low + (interval.high - interval.low)/2
    xval = doc.createElement(kind)
    xval.setAttribute("key", name)
    xval.setAttribute("value", str(value))
    return [xval]

  def to_xes(self, doc):
    xevent = doc.createElement('event')
    xevent.appendChild(self.activity_to_xes(doc))
    #xevent.appendChild(self.time_to_xes(doc))
    for (name, dval) in self._data.items():
      for d in self.data_value_to_xes(doc, name, dval):
        xevent.appendChild(d)
    return xevent


class TraceAbstraction:
  def __init__(self, events, prob = None):
    self._events = events
    self._probability = prob
  
  def __str__(self):
    s = ""
    for e in self._events:
      s += " " + str(e)
    return s

  def __len__(self):
    return len(self._events)

  def __getitem__(self, key):
    return self._events[key]
  
  def to_xes(self, doc):
    xtrace = doc.createElement('trace')
    if self._probability:
      xtrace.setAttribute("probability", str(self._probability))
    for event in self._events:
      xevent = event.to_xes(doc)
      xtrace.appendChild(xevent)
    return xtrace


def traces_to_xes(traces):
  doc = xml.dom.minidom.parseString("<log/>")
  root = doc.documentElement
  root.setAttribute("xes.version", "1849-2016")
  root.setAttribute("xes.features", "nested-attributes")
  root.setAttribute("xmlns", "http://www.xes-standard.org/")
  for trace in traces:
    xtrace = trace.to_xes(doc)
    root.appendChild(xtrace)
  return root