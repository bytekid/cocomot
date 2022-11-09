import sys
import time
import random
from pm4py.objects.log.importer.xes import importer as xes_importer
import json
import getopt
import copy

from dpn.read import read_json_input, read_pnml_input
from cluster.partitioning import NaivePartitioning, IntervalPartitioning
from dpn.dpn import DPN
from dpn.expr import Expr
from utils import *
from mining.synth import *

THRESH = 0.9

# complete valuations such that values are propagated
def preprocess_trace(trace):
  simple_trace = []
  valuation = {}
  for e in trace:
    ignore = ["concept:name", "time:timestamp", "lifecycle:transition", "org:resource"]
    written = dict([(v, e[v]) for v in e if v not in ignore])
    if "concept:name" in e:
      event = { "label" : e["concept:name"], "written": written, "valuation": valuation }
      simple_trace.append(event)
    val = dict([ (k,v) for (k,v) in valuation.items() ])
    for v in written:
      val[v] = written[v]
    valuation = val
  return simple_trace

def preprocess_log(log):
  log_processed = []
  for trace in log:
    log_processed.append(preprocess_trace(trace))
  return log_processed

def synthesizers(vtype, do_read):
  if vtype == VarType.int:
    return [BoundSynthesizer(do_read), LinCombSynthesizer("==", do_read), LinCombSynthesizer(">=", do_read)]
  elif vtype == VarType.real:
    return [BoundSynthesizer(do_read), LinCombSynthesizer("==", do_read), LinCombSynthesizer(">=", do_read)]
  return [SMTFunctionSynthesizer()]

def discover_write_guards(activity, log):
  # log is list of (trace, count) pairs
  logpart = log[:200]
  events = [e for (t, _) in logpart for e in t if e["label"] == activity]
  written = set([ v for e in events for v in e["written"]])
  for v in written:
    #if not (activity == "Payment" and v == "totalPaymentAmount"):
    #  continue
    vals = list(set([ e["written"][v] for e in events if v in e["written"] ]))
    vtype = val_type(vals[0])
    if len(vals) == 1:
      print("%s writes %s (%s)" % (activity, v, VarType.to_str(vtype)))
      print("  single value: " + str(vals[0]))
      continue
    for synth in synthesizers(vtype, False):
      synth.generate(v, activity, log)
      if synth.fitness() > THRESH:
        print("%s writes %s (%s)" % (activity, v, VarType.to_str(vtype)))
        synth.print()
      sys.stdout.flush()

def discover_read_guards(activity, log):
  # log is list of (trace, count) pairs
  logpart = log[:200]
  events = [e for (t, _) in logpart for e in t if e["label"] == activity]
  read = set([ v for e in events for v in e["valuation"]])
  for v in read:
    vals = list(set([ e["valuation"][v] for e in events if v in e["valuation"] ]))
    vtype = "int" if isinstance(vals[0], int) else "float" \
      if isinstance(vals[0], float) else "string"
    if vtype == "string":
      continue
    for synth in synthesizers(vtype, True):
      synth.generate(v, activity, log)
      if synth.fitness() > THRESH:
        print("%s reads %s (%s)" % (activity, v, vtype))
        synth.print()


def discover_nonoverlapping_decision(ts, log):
  #synth = SMTDecisionSynthesizer()
  #synth.generate(ts, log)
  pass

def decision_points(dpn):
  dps = [ p["id"] for p in dpn.places() if len(dpn.post(p["id"])) > 1 ]
  trans = dict([ (t["id"], t) for t in dpn.transitions() ])
  return [ (pid, [ trans[t]["label"] for t in dpn.post(pid)]) for pid in dps ]


def unique_log(log):
  def trace_data(t):
    labels = [e["label"] for e in t]
    writtens = [tuple([ e["written"][k] for k in sorted(e["written"].keys())]) for e in t]
    return (len(t), tuple(labels), tuple(writtens))
  log_data = [ (t, trace_data(t)) for t in log ]
  log_sorted = sorted(log_data, key=lambda t: hash(t[1]))
  i = 0
  uniques = []
  while i < len(log_sorted):
    (trace, tdata) = log_sorted[i]
    j = i + 1
    while j < len(log_sorted) and log_sorted[j][1] == tdata:
      j += 1
    uniques.append((trace, j-i))
    i = j
  return uniques


if __name__ == "__main__":
  logfile = sys.argv[1]
  log = xes_importer.apply(logfile)
  log = preprocess_log(log)
  log = unique_log(log)
  print("%d unique traces" % len(log))
  sys.stdout.flush()
  #random.shuffle(log)
  dpn = DPN(read_pnml_input(sys.argv[2]))

  labels = set([e["label"] for (trace, _) in log for e in trace ])
  for l in labels:
    discover_write_guards(l, log)
    discover_read_guards(l, log)
  for (p, ts) in decision_points(dpn):
    discover_nonoverlapping_decision(ts, log)
  #print("decision points", decision_points(dpn))
