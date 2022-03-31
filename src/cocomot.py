import sys
import time
import multiprocessing
from pm4py.objects.log.importer.xes import importer as xes_importer
import json
import getopt

#from smt.cvc5solver import CVC5Solver
from smt.ysolver import YicesSolver
from smt.z3solver import Z3Solver
from dpn.read import read_json_input, read_pnml_input
from cluster.partitioning import NaivePartitioning, IntervalPartitioning
from dpn.dpn import DPN
from encoding.encoding import Encoding
from encoding.encoding_exhaustive import ExhaustiveEncoding
from dpn.expr import Expr
import uncertainty.read
from uncertainty.encoding import UncertaintyEncoding
from utils import pad_to, spaces

### printing

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
        a += pad_to(str(value), tab) + " "
      else:
        a += spaces(tab+1)
    print(a)


def print_trace_distance(index, trace, t_enc, ts_solv, cnt, distance):
  print("DISTANCE : " + str(distance), flush=True)
  print("time/encode: %.2f  time/solve: %.2f" % (t_enc, ts_solv))

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

def print_alignments_json(alignments):
  for (trace, dist, alignment) in alignments:
    for a in (alignment if isinstance(alignment, list) else [alignment]):
      if not a:
        continue
      run = a["run"]
      run["transitions"] = [ label for (_,label) in run["transitions"]]
      del run["valuations"]
      all_mlists = []
      for m in run["markings"]:
        mlist = []
        for (p,c) in m.items():
          for j in range(0,c):
            mlist.append(p)
        all_mlists.append(mlist)
      run["markings"] = all_mlists
    data = {"trace" : trace[1], "alignments": alignment}
    print(json.dumps(data, indent=2))

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

def conformance_check_trace_many(encoding, trace_data, cost_bound):
  (index, trace, cnt) = trace_data
  t_start = time.perf_counter()
  (dist, dconstr) = encoding.edit_distance(trace)
  t_encode2 = time.perf_counter() - t_start
  encoding.solver().require([dconstr])
  alignments = []
  print("\n##### CONFORMANCE CHECK TRACE %d (%d instances, length %d)" % \
    (index, cnt, len(trace)))
  model = encoding.solver().minimize(dist, cost_bound)
  while model != None and model.eval_int(dist) <= cost_bound:
    alignment_decoded = encoding.decode_alignment(trace, model)
    print("\nDISTANCE:", alignment_decoded["cost"])
    print_trace_distance_verbose(encoding._dpn, trace, alignment_decoded)
    alignments.append(alignment_decoded)
    encoding.solver().require([encoding.negate(trace, alignment_decoded, model)])
    model.destroy()
    model = encoding.solver().minimize(dist, cost_bound)
  t_solve = encoding.solver().t_solve
  return (-1, alignments, t_encode2, t_solve)


def conformance_check_trace(encoding, trace_data, verbose):
  (index, trace, cnt) = trace_data
  t_start = time.perf_counter()
  (dist, dconstr) = encoding.edit_distance(trace)
  t_encode2 = time.perf_counter() - t_start

  encoding.solver().require([dconstr])
  if verbose > 0:
    print("##### CONFORMANCE CHECK TRACE %d (%d instances, length %d)" % \
    (index, cnt, len(trace)))
    sys.stdout.flush()

  #FIXME step_bound may in general not be valid upper bound due to writes
  model = encoding.solver().minimize(dist, encoding.step_bound())
  t_solve = encoding.solver().t_solve
  if model == None: # timeout
    return (None, None, t_encode2, t_solve)

  distance = model.eval_int(dist)

  if verbose > 1:
    alignment_decoded = encoding.decode_alignment(trace, model)
    print_trace_distance(index, trace, t_encode2, t_solve, cnt, distance)
    print_trace_distance_verbose(encoding._dpn, trace, alignment_decoded)
  elif verbose > 0:
    print_trace_distance(index, trace, t_encode2, t_solve, cnt, distance)
    alignment_decoded = {}
  else:
    alignment_decoded = encoding.decode_alignment(trace, model)
  model.destroy()
  return (distance, alignment_decoded, t_encode2, t_solve)

# conformance check one trace
def create_encoding(solver, trace_length, dpn, uncertain=False, all_sol=False):
  # estimate of upper bound on steps to be considered: length of trace + length
  # of shortest accepting path
  # FIXME step bound if not state machine
  step_bound = trace_length + dpn.shortest_accepted() + 2
  dpn.compute_reachable(step_bound)

  if uncertain:
    encoding = UncertaintyEncoding(dpn, solver, step_bound, uncertain)
  elif all_sol:
    encoding = ExhaustiveEncoding(dpn, solver, step_bound)
  else:
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
  return (encoding, t_encode1)

# conformance check one trace
def conformance_check_single_trace(solver, trace_record, dpn, verbose=0, many=None):
  (_, trace, _) = trace_record
  (encoding, _) = create_encoding(solver, len(trace), dpn, all_sol=many)
  return conformance_check_trace(encoding, trace_record, verbose)

# conformance check multiple traces of same length
def conformance_check_traces(solver, traces, dpn, verbose=0, many=None):
  (enc, t_enc1) = create_encoding(solver, len(traces[0][1]), dpn, all_sol=many)

  results = []
  if len(traces) == 1:
    res = conformance_check_trace(enc, traces[0], verbose) if not many \
      else conformance_check_trace_many(enc, traces[0], many)
    results.append((traces[0], res))
  else:
    for trace in traces:
      solver.push()
      res = conformance_check_trace(enc, trace,verbose) if not many \
        else conformance_check_trace_many(enc, trace, many)
      results.append((trace, res))
      solver.pop()
  return results, t_enc1

# multi- or anti-alignment conformance checking
def conformance_check_aggregated(log, dpn, verbose, anti):
  log = preprocess_log(log, dpn)
  tracepart = NaivePartitioning(log)
  length = anti if anti else max([ len(t) for (t,_) in tracepart.partitions ])

  solver = Z3Solver()
  # switch between multi- and anti-alignment
  dist_aggregate = solver.max if not anti else solver.min
  optimize = solver.minimize if not anti else solver.maximize

  (encoding, _) = create_encoding(solver, length, dpn)
  dopt = None
  for (trace, count) in tracepart.partitions:
    (dist, dconstr) = encoding.edit_distance(trace)
    solver.require([dconstr])
    dopt = dist_aggregate(dopt, dist) if dopt != None else dist

  model = optimize(dopt, encoding.step_bound())
  if model == None: # timeout
    return (None, t_encode2, 0)

  cost = model.eval_int(dopt)
  print("%s-ALIGNMENT COST %d" % ("ANTI" if anti else "MULTI", cost))
  alignments = []
  for (trace, count) in tracepart.partitions:
    a = encoding.decode_alignment(trace, model)
    alignments.append(a)
    print_trace_distance_verbose(dpn, trace, a)
  model.destroy()
  return alignments, cost

# multi-alignment conformance checking
def conformance_check_multi(log, dpn, verbose=0):
  return conformance_check_aggregated(log, dpn, verbose, anti=None)

# anti-alignment conformance checking
def conformance_check_anti(log, dpn, verbose, anti_bound):
  return conformance_check_aggregated(log, dpn, verbose, anti=anti_bound)

def read_log(logfile):
  if "uncertainty" in open(logfile, "r").read():
    return (uncertainty.read.xes(logfile), True)
  else:
    return (xes_importer.apply(logfile), False)

### main
def cocomot_uncertain(dpn, log, ukind, verbose=1):
  solver = Z3Solver()
  results = []
  for trace in log:
    (encoding, _) = create_encoding(solver, len(trace), dpn, uncertain=ukind)
    solver.require([encoding.trace_constraints(trace)])
    if ukind == "min":
      (dist, dconstr) = encoding.edit_distance_min(trace)
    else:
      (dist, dconstr) = encoding.edit_distance_fitness(trace)
    solver.require([dconstr])
    model = encoding.solver().minimize(dist, encoding.step_bound()+10)
    distance = None if model == None else model.eval_real(dist)
    result = encoding.decode_alignment(trace, model)
    print("distance", distance)
    if verbose > 0:
      print(result)
      print_trace_distance_verbose(encoding._dpn, result["trace"], result)
    results.append(distance)
    model.destroy()
  return results

def work(job):
  solver = YicesSolver()
  (i, (trace, cnt), dpn) = job
  res, t_enc = conformance_check_traces(solver, [(i, trace, cnt)], dpn)
  (distance, _, t_enc, t_solv) = res[0][1]
  solver.destroy()
  return (i, trace, cnt, distance, t_enc, t_solv)

def cocomot(dpn, log, numprocs=1, verbose=1, many=None):
  # preprocessing
  log = preprocess_log(log, dpn)
  if len(log) > 1:
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
  if len(log) > 1:
    print("equivalence classes naive: %d, intervals: %d (clustering time %.2f)" % \
      (naive_part.partition_count(), interval_part.partition_count(), t_cluster))
  i = 0
  parts = interval_part.partitions
  if numprocs == 1:
    solver = Z3Solver() # YicesSolver() # CVC5Solver()  # 
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
      res,tenc = conformance_check_traces(solver,same_len_traces,dpn, verbose=verbose, many = many)
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
    jobs = [ (i, t, dpn) for (i,t) in enumerate(parts) ]
    #for j in jobs:
    #  work(j)

    pool = multiprocessing.Pool(numprocs)
    results = pool.map_async(work, jobs)
    pool.close()
    pool.join()
    for r in results.get():
      (i, trace, cnt, d, t_enc, t_solv) = r
      if d != None:
        print_trace_distance(i, trace, t_enc, t_solv, cnt, d)
        distances[d] = distances[d] + 1 if d in distances else 1
      else:
        timeouts += 1
      ts_encode.append(t_enc)
      ts_solve.append(t_solv)
    
  
  ts_solve.sort()
  ts_encode.sort()
  if verbose > 0 and len(log) > 1:
    mid = int(len(ts_encode)/2)
    print("encoding time: total %.2f  avg %.2f median %.2f" % \
      (sum(ts_encode ), sum(ts_encode)/len(ts_encode), ts_encode[mid]))
    print("solving time:  total %.2f  avg %.2f median %.2f" % \
      (sum(ts_solve ), sum(ts_solve)/len(ts_solve), ts_solve[mid]))
    if not many:
      for (d, cnt) in distances.items():
        print("distance %d: %d" % (d, cnt))
      print("timeouts: %d" % timeouts)
  elif verbose > 1:
    print_alignments_json(alignments)
  YicesSolver.shutdown()

def process_args(argv):
  usage = "cocomot.py <model_file> <log_file> [-p <property_string> | -s] [-x <number>]"
  model_file = None
  log_file = None
  many = None
  multi = None
  anti = None
  numprocs = 1
  uncertainty = None
  verbose = 1
  try:
    opts, args = getopt.getopt(argv,"hmu:v:d:l:n:x:a:")
  except getopt.GetoptError:
    print(usage)
    sys.exit(2)
  for (opt, arg) in opts:
    if opt == '-h':
      print(usage)
      sys.exit()
    elif opt == "-d":
      model_file = arg
    elif opt == "-l":
      log_file = arg
    elif opt == "-x":
      many = int(arg)
    elif opt == "-u":
      uncertainty = arg
    elif opt == "-m":
      multi = True
    elif opt == "-a":
      anti = int(arg)
    elif opt == "-v":
      verbose = int(arg)
    elif opt == "-n":
      numprocs = int(arg)
  return {
    "anti": anti,
    "log": log_file,
    "many": many,
    "model": model_file, 
    "multi": multi,
    "numprocs":numprocs,
    "uncertainty": uncertainty,
    "verbose": verbose
  }

if __name__ == "__main__":
  ps = process_args(sys.argv[1:])
  dpn = DPN(read_pnml_input(ps["model"]))
  (log, has_uncertainty) = read_log(ps["log"])
  if ps["multi"]:
    conformance_check_multi(log, dpn, ps["verbose"])
  elif ps["anti"]:
    conformance_check_anti(log, dpn, ps["verbose"], ps["anti"])
  elif has_uncertainty:
    ps["uncertainty"] = "min" if not ps["uncertainty"] else ps["uncertainty"] 
    cocomot_uncertain(dpn, log, ps["uncertainty"], ps["verbose"])
  else:
    cocomot(dpn, log, ps["numprocs"], ps["verbose"], ps["many"])
  