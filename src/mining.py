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
from utils import pad_to, spaces
from mining.synth import *


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
  if vtype == "int":
    return [BoundSynthesizer(do_read)]
  elif vtype == "float":
    return [BoundSynthesizer(do_read), LinCombSynthesizer(do_read)]
  return []

def discover_write_guards(activity, logpart, log):
  # log is list of (trace, count) pairs
  events = [e for (t, _) in logpart for e in t if e["label"] == activity]
  written = set([ v for e in events for v in e["written"]])
  for v in written:
    #if not (activity == "Payment" and v == "totalPaymentAmount"):
    #  continue
    vals = list(set([ e["written"][v] for e in events if v in e["written"] ]))
    vtype = "int" if isinstance(vals[0], int) else "float" \
      if isinstance(vals[0], float) else "string"
    if vtype == "string":
      continue
    print("%s writes %s (%s)" % (activity, v, vtype))
    #if isinstance(vals[0], str):
    #  print("  %d values" % len(vals))
    #else:
    #  print("  %d values (min %.2f, max %.2f)" % (len(vals), min(vals), max(vals)))
    #if len(vals) < 10:
    #  print("  ", vals)
    if len(vals) == 1:
      print("  single value: " + str(vals[0]))
      continue
    for synth in synthesizers(vtype, False):
      synth.generate(v, activity, events, log)
      synth.print()

def discover_read_guards(activity, logpart, log):
  # log is list of (trace, count) pairs
  events = [e for (t, _) in logpart for e in t if e["label"] == activity]
  read = set([ v for e in events for v in e["valuation"]])
  for v in read:
    vals = list(set([ e["valuation"][v] for e in events if v in e["valuation"] ]))
    vtype = "int" if isinstance(vals[0], int) else "float" \
      if isinstance(vals[0], float) else "string"
    if vtype == "string":
      continue
    print("%s reads %s (%s)" % (activity, v, vtype))
    for synth in synthesizers(vtype, True):
      synth.generate(v, activity, events, log)
      synth.print()
    
    

def unique_log(log):
  def trace_data(t):
    labels = [e["label"] for e in t]
    writtens = [tuple([ e["written"][k] for k in sorted(e["written"].keys())]) for e in t]
    return (len(t), labels, writtens)
  log_data = [ (t, trace_data(t)) for t in log ]
  log_sorted = sorted(log_data, key=lambda t: t[1])
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
  random.shuffle(log)
  logpart = log[:500]

  labels = set([e["label"] for (trace, _) in logpart for e in trace ])
  for l in labels:
    discover_write_guards(l, logpart, log)
    discover_read_guards(l, logpart, log)
