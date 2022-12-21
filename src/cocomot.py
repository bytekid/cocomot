import sys
import time
import multiprocessing
import pm4py
from pm4py.objects.log.importer.xes import importer as xes_importer
import json
import getopt
from collections import defaultdict

from smt.ysolver import YicesSolver
from smt.z3solver import Z3Solver
from smt.omsolver import OptiMathsatSolver
#from smt.cvc5solver import CVC5Solver
from dpn.read import read_json_input, read_pnml_input
from cluster.partitioning import NaivePartitioning, IntervalPartitioning
from dpn.dpn import DPN
from encoding.encoding import Encoding
from encoding.encoding_exhaustive import ExhaustiveEncoding
from dpn.expr import Expr
import uncertainty.read
from uncertainty.encoding import UncertaintyEncoding
from uncertainty.trace import UncertainTrace, UncertainLog
from uncertainty.uncertainize import all as uncertainize_all, extending as uncertainty_extending
from utils import pad_to, spaces
from options import default as default_options

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
  alldata = []
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
    alldata.append(data)
  print(json.dumps(alldata, indent=2))

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

def conformance_check_trace_many(encoding, trace_data, opts):
  cost_bound = opts["many"]
  verbose = opts["verbose"]
  (index, trace, cnt) = trace_data
  t_start = time.perf_counter()
  (dist, dconstr) = encoding.edit_distance(trace)
  t_encode2 = time.perf_counter() - t_start
  solver = encoding.solver()
  solver.require([dconstr])
  alignments = []
  if verbose > 0:
    print("\n##### CONFORMANCE CHECK TRACE %d (%d instances, length %d)" % \
      (index, cnt, len(trace)))
  model = solver.minimize(dist, cost_bound)
  while model != None and model.eval_int(dist) <= cost_bound:
    alignment_decoded = encoding.decode_alignment(trace, model)
    if verbose > 0:
      print("\nDISTANCE:", alignment_decoded["cost"])
      print_trace_distance_verbose(encoding._dpn, trace, alignment_decoded)
    alignments.append(alignment_decoded)
    solver.require([encoding.negate(trace, alignment_decoded, model,all=False)])
    model.destroy()
    model = solver.minimize(dist, cost_bound) if solver.is_sat() else None
  t_solve = solver.t_solve
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
def conformance_check_traces(solver, traces, dpn, opts):
  (verbose, many) = (opts["verbose"], opts["many"])
  (enc, t_enc1) = create_encoding(solver, len(traces[0][1]), dpn, all_sol=many)

  results = []
  if len(traces) == 1:
    res = conformance_check_trace(enc, traces[0], verbose) if not many \
      else conformance_check_trace_many(enc, traces[0], opts)
    results.append((traces[0], res))
  else:
    for trace in traces:
      solver.push()
      res = conformance_check_trace(enc, trace,verbose) if not many \
        else conformance_check_trace_many(enc, trace, opts)
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


### uncertainty
def make_uncertainty_solver(opts):
  if opts["solver"] == None:
    return YicesSolver() if opts["uncertainty"] =="min" else OptiMathsatSolver()
  else:
    if opts["solver"] == "yices":
      return YicesSolver()
    elif opts["solver"] == "z3":
      return Z3Solver()
    elif opts["solver"] == "z3-inc":
      return Z3Solver(incremental=True)
    elif opts["solver"] == "optimathsat":
      return OptiMathsatSolver()
    elif opts["solver"] == "optimathsat-inc":
      return OptiMathsatSolver(incremental=True)

def work_uncertain(job):
  (i, trace, dpn, opts, solver) = job
  ukind, verbose = opts["uncertainty"], opts["verbose"]
  own_solver = (solver == None)
  if not solver:
    solver = make_uncertainty_solver(opts)

  solver.push()
  if not isinstance(trace, UncertainTrace):
    trace = UncertainTrace.from_certain_trace(preprocess_trace(trace, dpn))
  trace.normalize_time() # replace timestamps by floats
  (encoding, t_enc) = create_encoding(solver, len(trace), dpn, uncertain=ukind)
  solver.push()
  solver.require([encoding.trace_constraints(trace)])
  t_start = time.perf_counter()
  if ukind == "min":
    (dist, dconstr) = encoding.edit_distance_min(trace)
  else:
    (dist, dconstr) = encoding.edit_distance_fitness(trace)
  t_enc =  t_enc + (time.perf_counter() - t_start)
  solver.require([dconstr])
  model = solver.minimize(dist, encoding.step_bound()+10)
  t_solve = solver.t_solve
  distance = None if model == None else round(model.eval_real(dist),2)
  result = encoding.decode_alignment(trace, model)
  if verbose > 0:
    print("%d. distance" % i, distance)
    print("encoding time: %.2f" % t_enc)
    print("solving time: %.2f" % t_solve)
    #print(result)
    print_trace_distance_verbose(encoding._dpn, result["trace"], result)
  sys.stdout.flush()
  model.destroy()
  solver.pop()
  solver.reset()
  if own_solver:
    solver.destroy()
  return (distance, t_enc, t_solve)

def cocomot_uncertain(dpn, log, os):
  (ukind, verbose, numprocs) = (os["uncertainty"], os["verbose"],os["numprocs"])
  ts_encode = []
  ts_solve = []
  distances = defaultdict(lambda: 0)
  if numprocs == 1:
    results = []
    reals = []
    solver = make_uncertainty_solver(os)
    for (i, trace) in enumerate(log):
      #reals+= trace.get_realizations()
      results.append(work_uncertain((i, trace, dpn, os, solver)))
    solver.destroy()
    for (d, t_enc, t_solv) in results:
      ts_encode.append(t_enc)
      ts_solve.append(t_solv)
      d = str(d)
      distances[d] += 1
    #print(len(reals),"realizations")
    #log = UncertainLog([UncertainTrace(r) for r in reals])
    #xml = log.to_xes()
    #f = open("/home/bytekid/tools/cocomot/data/uncertainty/road_fines/realizations/time_02.xes", "a")
    #f.write("<?xml version='1.0' encoding='UTF-8'?>" + xml.toprettyxml())
    #f.close()
    #print([str(UncertainTrace(r)) for r in reals])
  else:
    print("Parallel checking with %d processes ..." % numprocs)
    jobs = [ (i, t, dpn, opts, None) for (i,t) in enumerate(log) ]
    #for j in jobs:
    #  work(j)
    pool = multiprocessing.Pool(numprocs)
    results = pool.map_async(work_uncertain, jobs)
    pool.close()
    pool.join()
    sys.stdout.flush()
    for (d, t_enc, t_solv) in results.get():
      if d != None:
        distances[d] = distances[d] + 1 if d in distances else 1
      else:
        timeouts += 1
      ts_encode.append(t_enc)
      ts_solve.append(t_solv)
      if d in distances:
        distances[d] += 1
  mid = int(len(ts_encode)/2)
  if verbose > 0:
    print("encoding time: total %.2f  avg %.2f median %.2f" % \
      (sum(ts_encode ), sum(ts_encode)/len(ts_encode), ts_encode[mid]))
    print("solving time:  total %.2f  avg %.2f median %.2f" % \
      (sum(ts_solve ), sum(ts_solve)/len(ts_solve), ts_solve[mid]))
    for (d, cnt) in distances.items():
      print("distance %s: %d" % (d, cnt))
  return list(distances.keys())


def work(job):
  solver = YicesSolver()
  (i, (trace, cnt), dpn, opts) = job
  res, t_enc = conformance_check_traces(solver, [(i, trace, cnt)], dpn, opts)
  (distance, _, t_enc, t_solv) = res[0][1]
  solver.destroy()
  return (i, trace, cnt, distance, t_enc, t_solv)

def cocomot(dpn, log, opts):
  # preprocessing
  (numprocs, verbose, many) = (opts["numprocs"], opts["verbose"], opts["many"])
  log = preprocess_log(log, dpn)
  if len(log) > 1 and verbose > 0:
    print("number of traces: %d" % len(log))

  ts_encode = []
  ts_solve = []
  distances = {}
  alldistances = {}
  timeouts = 0
  alignments = []

  # get unique traces by data
  t_start = time.perf_counter()
  naive_part = NaivePartitioning([ (t,1) for t in log ])
  interval_part = IntervalPartitioning(dpn, naive_part.representatives())

  t_cluster =  time.perf_counter() - t_start
  if len(log) > 1 and verbose > 0:
    print("equivalence classes naive: %d, intervals: %d (clustering time %.2f)" % \
      (naive_part.partition_count(), interval_part.partition_count(), t_cluster))
  i = 0
  parts = interval_part.partitions

  if numprocs == 1:
    solver = YicesSolver() # CVC5Solver()  # Z3Solver() # 
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
      res,tenc = conformance_check_traces(solver, same_len_traces, dpn, opts)
      for (j, (trace, (d, a, t_enc, t_solv))) in enumerate(res):
        if d == None:
          timeouts += 1
        else:
          distances[d] = distances[d] + 1 if d in distances else 1
          cnt = parts[i - len(same_len_traces) + 1 + j][1]
          alldistances[d] = alldistances[d] + cnt if d in alldistances else cnt
        ts_encode.append(t_enc)
        ts_solve.append(t_solv)
        alignments.append((trace, d, a))
      solver.reset()
      i = i + 1
    solver.destroy()
  else:
    print("Parallel checking with %d processes ..." % numprocs)
    jobs = [ (i, t, dpn, opts) for (i,t) in enumerate(parts) ]
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
        alldistances[d] = alldistances[d] + cnt if d in alldistances else cnt
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
        print("distance %d: %d (%d overall)" % (d, cnt, alldistances[d]))
      print("timeouts: %d" % timeouts)
  if opts["json"]:
    print_alignments_json(alignments)
  YicesSolver.shutdown()

def process_args(argv):
  usage = "cocomot.py <model_file> <log_file> [-p <property_string> | -s] [-x <number>]"
  opts = default_options
  try:
    optargs, args = getopt.getopt(argv,"hjmo:u:v:d:l:n:x:a:s:")
  except getopt.GetoptError:
    print(usage)
    sys.exit(1)
  for (opt, arg) in optargs:
    if opt == '-h':
      print(usage)
      sys.exit()
    elif opt == "-d":
      opts["model"] = arg
    elif opt == "-l":
      opts["log"] = arg
    elif opt == "-x":
      opts["many"] = int(arg)
    elif opt == "-u":
      if arg not in ["fit", "min"]:
        print(usage)
        sys.exit(1)
      opts["uncertainty"] = arg
    elif opt == "-m":
      opts["multi"] = True
    elif opt == "-j":
      opts["json"] = True
      opts["verbose"] = 0
    elif opt == "-a":
      opts["anti"] = int(arg)
    elif opt == "-o":
      args = ["indet", "act", "time", "data", "mixed"]
      if not (arg in args):
        print ("arguments supported for -o are ", args)
        sys.exit(1)
      opts["obfuscate"] = arg
    elif opt == "-s":
      args = ["yices", "optimathsat", "optimathsat-inc", "z3", "z3-inc"]
      if not (arg in args):
        print ("arguments supported for -s are ", args)
        sys.exit(1)
      opts["solver"] = arg
    elif opt == "-v":
      opts["verbose"] = int(arg)
    elif opt == "-n":
      opts["numprocs"] = int(arg)
  return opts

if __name__ == "__main__":
  ps = process_args(sys.argv[1:])
  (log, has_uncertainty) = read_log(ps["log"])
  if ps["obfuscate"]:
    log = uncertainty.read.xes(ps["log"])
    uncertainty_extending(log, ps["obfuscate"])
  else:
    dpn = DPN(read_pnml_input(ps["model"]))
    if ps["multi"]:
      conformance_check_multi(log, dpn, ps["verbose"])
    elif ps["anti"]:
      conformance_check_anti(log, dpn, ps["verbose"], ps["anti"])
    elif ps["uncertainty"]: # has_uncertainty
      cocomot_uncertain(dpn, log, ps)
    else:
      cocomot(dpn, log, ps)
  YicesSolver.shutdown()
  