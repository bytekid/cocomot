import sys
import time
import multiprocessing
import pm4py
from pm4py.objects.log.importer.xes import importer as xes_importer
import json
import getopt

from smt.ysolver import YicesSolver
from smt.z3solver import *
from dpn.read import read_json_input, read_pnml_input
from cluster.partitioning import NaivePartitioning, IntervalPartitioning
from dpn.dpn import DPN
from encoding.encoding import Encoding
from dpn.expr import Expr

### printing
def spaces(n):
  return "" if n <= 0 else " " + spaces(n-1) 


def fill_to(s, n):
  return s + spaces(n - len(s)) if len(s) < n else s[:n]


def print_sequence(dpn, seq, tab = 12):
  transs = dict([ (t["id"], t) for t in dpn.transitions() ])
  a = spaces(tab+1)
  # print transition label sequence (or >> for skip step)
  for i in range(0, len(seq)):
    a += fill_to(seq[i]["label"], tab) + " " if seq[i] else "  >>"+spaces(tab-3)
  print(a)
  # print valuation sequence for each variable
  for v in dpn.variables():
    name = v["name"]
    a = fill_to(name, tab) + " "
    for i in range(0, len(seq)):
      if seq[i] == None: # is a skip step >>
        a += spaces(tab+1)
        continue

      val = seq[i]["valuation"]
      j = i - 1 # search last valuation
      while j > 0 and seq[j] == None:
        j -= 1
      val_pre = seq[j]["valuation"] if j >= 0 else None
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
        a += fill_to(str(value), tab) + " "
      else:
        a += spaces(tab+1)
    print(a)


def print_trace_distance(index, trace, t_enc, ts_solv, cnt, distance):
  print("##### CONFORMANCE CHECK TRACE %d (%d instances, length %d)" % \
    (index, cnt, len(trace)))
  print("DISTANCE : " + str(distance), flush=True)
  print("time/encode: %.2f  time/solve: %.2f" % (t_enc, ts_solv))

def print_trace_distance_verbose(dpn, trace, decoding):
  places = dict([ (p["id"], p) for p in dpn.places() ])
  transs = dict([ (p["id"], p) for p in dpn.transitions() ])
  valuations = []
  print("\nMARKING:")
  for i in range(0, len(decoding["markings"])):
    marking = ""
    for (p,count) in list(decoding["markings"][i].items()):
      for c in range(0, count):
        marking = marking + (" " if marking else "") + str(places[p]["name"])
    print("  %d: %s" % (i, marking))

  # shift model and log sequences to account for >> in alignment
  modelseq = []
  idx = 0
  for i in range(0, len(decoding["alignment"])):
    if decoding["alignment"][i] != "log":
      (tid, tlab) = decoding["transitions"][idx]
      if tlab != "tau":
        val = decoding["valuations"][idx + 1]
        step = { "id": tid, "label": tlab, "valuation": val }
        modelseq.append(step)
      idx += 1
    else:
      modelseq.append(None)
  traceseq = []
  idx = 0
  for i in range(0, len(decoding["alignment"])):
    if decoding["alignment"][i] != "model":
      traceseq.append(trace[idx])
      idx += 1
    else:
      traceseq.append(None)

  print("LOG SEQUENCE:")
  print_sequence(dpn, traceseq)
  print("\nMODEL SEQUENCE:")
  print_sequence(dpn, modelseq)
  sys.stdout.flush()

def print_alignments_json(alignments):
  for (trace, dist, alignment) in alignments:
    for a in (alignment if isinstance(alignment, list) else [alignment]):
      a["transitions"] = [ label for (_,label) in a["transitions"]]
      del a["valuations"]
      all_mlists = []
      print(a["markings"])
      for m in a["markings"]:
        mlist = []
        for (p,c) in m.items():
          for j in range(0,c):
            mlist.append(p)
        all_mlists.append(mlist)
      a["markings"] = all_mlists
    data = {"trace" : trace[1], "alignments": alignment}

### preprocessing
def preprocess_trace(trace, dpn):
  simple_trace = []
  for e in trace:
    valuation = {}
    for v in dpn.variables():
      if v["name"] in e:
        val = e[v["name"]]
        valuation[v["name"]] = val if not isinstance(val,str) else \
          0 if val == "NIL" else ord(val[0])
    if "concept:name" in e:
      simple_trace.append({"label" : e["concept:name"], "valuation": valuation})
  return simple_trace


def preprocess_log(log, dpn):
  log_processed = []
  for trace in log:
    log_processed.append(preprocess_trace(trace, dpn))
  return log_processed

def conformance_check_trace_many(encoding, trace_data, verbosity, number):
  (index, trace, cnt) = trace_data
  t_start = time.perf_counter()
  (dist, dconstr) = encoding.edit_distance(trace)
  t_encode2 = time.perf_counter() - t_start
  encoding.solver().require([dconstr])
  alignments = []
  print("\n##### CONFORMANCE CHECK TRACE %d (%d instances, length %d)" % \
    (index, cnt, len(trace)))
  for i in range(0, number):
    model = encoding.solver().minimize(dist, encoding.step_bound())
    t_solve = encoding.solver().t_solve
    if model == None: # timeout
      print("(no further alignments found)")
      return (None, alignments, t_encode2, t_solve)
  
    alignment_decoded = encoding.decode_alignment(trace, model)
    print_trace_distance_verbose(encoding._dpn, trace, alignment_decoded)
    alignments.append(alignment_decoded)
    encoding.solver().require([encoding.negate(alignment_decoded)])
  return (-1, alignments, t_encode2, t_solve)

def conformance_check_trace(encoding, trace_data, verbosity):
  (index, trace, cnt) = trace_data
  t_start = time.perf_counter()
  (dist, dconstr) = encoding.edit_distance(trace)
  t_encode2 = time.perf_counter() - t_start

  encoding.solver().require([dconstr])

  #FIXME step_bound may in general not be valid upper bound due to writes
  model = encoding.solver().minimize(dist, encoding.step_bound())
  t_solve = encoding.solver().t_solve
  if model == None: # timeout
    return (None, t_encode2, t_solve)

  distance = model.eval_int(dist)

  if verbosity > 0:
    alignment_decoded = encoding.decode_alignment(trace, model)
    print_trace_distance(index, trace, t_encode2, t_solve, cnt, distance)
    print_trace_distance_verbose(encoding._dpn, trace, alignment_decoded)
  elif verbosity == 0:
    print_trace_distance(index, trace, t_encode2, t_solve, cnt, distance)
    alignment_decoded = {}
  else:
    alignment_decoded = encoding.decode_alignment(trace, model)

  return (distance, alignment_decoded, t_encode2, t_solve)


# conformance check multiple traces of same length
def conformance_check_traces(solver, traces, dpn, verbosity=0, many=None):
  # compute length of shortest path to final state 
  shortest_acc_path = dpn.shortest_accepted()
  # estimate of upper bound on steps to be considered: length of trace + length
  # of shortest accepting path
  # FIXME step bound if not state machine
  trace_length = len(traces[0][1])
  step_bound = trace_length + shortest_acc_path
  dpn.compute_reachable(step_bound)

  # create encoding object
  encoding = Encoding(dpn, solver, step_bound)

  # encoding parts
  t_start = time.perf_counter()
  f_initial = encoding.initial_state()
  f_trans_range = encoding.transition_range()
  f_tokens = encoding.transition_constraints()
  f_final = encoding.final_state()
  encoding.prepare_edit_distance(trace_length)
  solver.require([f_initial, f_trans_range, f_tokens, f_final])
  t_encode1 = time.perf_counter() - t_start

  results = []
  if len(traces) == 1:
    res = conformance_check_trace(encoding, traces[0], verbosity) if not many \
      else conformance_check_trace_many(encoding, traces[0], verbosity, many)
    results.append((traces[0], res))
  else:
    for trace in traces:
      solver.push()
      res = conformance_check_trace(encoding, trace,verbosity) if not many \
        else conformance_check_trace_many(encoding, trace, verbosity, many)
      results.append((trace, res))
      solver.pop()
  return results, t_encode1


### main
def cocomot(modelfile, logfile, numprocs, verbose, many):

  dpn = DPN(read_pnml_input(modelfile))
  #log = pm4py.read_xes(logfile)
  log = xes_importer.apply(logfile)


  # preprocessing
  log = preprocess_log(log, dpn)
  print("number of traces: %d" % len(log))

  ts_encode = []
  ts_solve = []
  distances = {}
  timeouts = 0
  alignments = []

  # get unique traces by data
  t_start = time.perf_counter()
  naive_part = NaivePartitioning(log)
  interval_part = IntervalPartitioning(dpn, naive_part.representatives())
  t_cluster =  time.perf_counter() - t_start
  print("equivalence classes naive: %d, intervals: %d (clustering time %.2f)" % \
    (naive_part.partition_count(), interval_part.partition_count(), t_cluster))
  i = 0
  parts = interval_part.partitions
  if numprocs == 1:
    solver = Z3Solver() # YicesSolver()
    i = 0
    while i < len(parts):
      (trace, cnt) = parts[i]
      same_len_traces = [(i, trace, cnt)]
      length = len(trace)
      while i+1 < len(parts) and len(parts[i+1][0]) == length:
        i = i+1
        (trace, cnt) = parts[i]
        same_len_traces.append((i, trace, cnt))
      #print("%d traces of length %d" % (len(same_len_traces), length))
      res,tenc = conformance_check_traces(solver,same_len_traces,dpn, verbosity=verbose, many = many)
      for (trace, (d, a, t_enc, t_solv)) in res:
        if d == None:
          timeouts += 1
        else:
          distances[d] = distances[d] + 1 if d in distances else 1
        ts_encode.append(t_enc)
        ts_solve.append(t_solv)
        alignments.append((trace, d, a))
      solver.reset()
      i = i + 1
    solver.destroy()
  else:
    print("Parallel checking with %d processes ..." % numprocs)
    jobs = enumerate(parts)

    def work(job):
      solver = YicesSolver()
      (i, (trace, cnt)) = job
      res, t_enc = conformance_check_traces(solver, [(i, trace, cnt)], dpn, verbosity=verbose)
      (distance, t_enc, t_solv) = res[0]
      solver.destroy()
      return (i, trace, cnt, distance, t_enc, t_solv)

    pool = multiprocessing.Pool(numprocs)
    results = pool.map_async(work, jobs)
    pool.close()
    pool.join()
    for r in results.get(10):
      (i, trace, cnt, d, t_enc, t_solv) = r
      if d != None:
        #print_trace_distance(i, trace, t_enc, t_solv, cnt, d)
        distances[d] = distances[d] + 1 if d in distances else 1
      else:
        timeouts += 1
      ts_encode.append(t_enc)
      ts_solve.append(t_solv)
    
  
  ts_solve.sort()
  ts_encode.sort()
  if verbose >= 0:
    mid = int(len(ts_encode)/2)
    print("encoding time: total %.2f  avg %.2f median %.2f" % \
      (sum(ts_encode ), sum(ts_encode)/len(ts_encode), ts_encode[mid]))
    print("solving time:  total %.2f  avg %.2f median %.2f" % \
      (sum(ts_solve ), sum(ts_solve)/len(ts_solve), ts_solve[mid]))
    for (d, cnt) in distances.items():
      print("distance %d: %d" % (d, cnt))
    print("timeouts: %d" % timeouts)
  else:
    print(alignments)
    print_alignments_json(alignments)
  YicesSolver.shutdown()

def process_args(argv):
  usage = "cocomot.py <model_file> <log_file> [-p <property_string> | -s] [-x]"
  model_file = None
  log_file = None
  many = False
  numprocs = 1
  verbose = 0
  try:
    opts, args = getopt.getopt(argv,"hxvm:l:n:")
  except getopt.GetoptError:
    print(usage)
    sys.exit(2)
  for (opt, arg) in opts:
    if opt == '-h':
      print(usage)
      sys.exit()
    elif opt == "-m":
      model_file = arg
    elif opt == "-l":
      log_file = arg
    elif opt == "-x":
      many = True
    elif opt == "-v":
      verbose = True
    elif opt == "-n":
      numprocs = int(arg)
  return {
    "model": model_file, 
    "log": log_file, 
    "verbose": verbose, 
    "numprocs":numprocs,
    "many": many
  }

if __name__ == "__main__":
  ps = process_args(sys.argv[1:])
  cocomot(ps["model"], ps["log"], ps["numprocs"], ps["verbose"], ps["many"])
  