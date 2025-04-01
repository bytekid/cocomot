import sys
import time
import os
import getopt

from objectcentric.opi import OPI
from objectcentric.read import ocel as read_ocel
from objectcentric.encoding import Encoding
from dpn.read import read_pnml_input
from smt.ysolver import YicesSolver
#from smt.cvc5solver import CVC5Solver
from smt.z3solver import Z3Solver

default_options = {
    "log": None,    # log file to be used
    "model": None,  # model input (DPN) 
    "skip existing": False,  # keep results
    "object": None, # specific object, do only trace that involes it
    "fixed objects": False, # use exactly the set of objects in the trace
    "numprocs": 1,  # number of processors to use in parallel
    "verbose": 1, # verbosity of output,
    "z": None # debug
  }

def file_for_trace(trace):
  return "out/" + trace.smallest_object() + ".txt"

def save_result(trace, content):
  f = open(file_for_trace(trace), "w")
  f.write(content)
  f.close()

def conformance_check(encoding, trace, options):
  t_start = time.perf_counter()
  dist = encoding.optimization_expression()
  encoding.get_solver().require([encoding.cache_constraints()])
  encoding.get_solver().require([encoding.edit_distance()])
  t_encode2 = time.perf_counter() - t_start

  optbound = encoding.get_step_bound() * encoding.get_max_objs_per_trans()
  model = encoding.get_solver().minimize(dist, max=optbound)
  #model = encoding.get_solver().check_sat(encoding.get_solver().eq(dist, encoding.get_solver().num(5)))
  t_solve = encoding.get_solver().t_solve
  if model == None: # timeout or bug
    print("no model found")
    return (None, t_encode2, t_solve, "unsatisfiable")

  distance = encoding.decode_alignment_cost(model)
  #distance = model.eval_int(dist) # not true if using run length
  out = encoding.decode(model)
  out += "ALIGNMENT COST: %d\n" % distance

  model.destroy()
  return (distance, t_encode2, t_solve, out)


def create_encoding(solver, trace, net, fixed_obj):
  net.reset()
  encoding = Encoding(solver, net, trace)
  t_start = time.perf_counter()
  encoding.create_variables()
  f_initial = encoding.initial_state(fixed_obj)
  f_trans = encoding.transition_range()
  f_obj_types = encoding.object_types()
  f_moving = encoding.moving_tokens()
  f_remaining = encoding.remaining_tokens()
  f_data = encoding.data_constraints()
  f_fresh = encoding.freshness()
  f_final = encoding.final_state()
  solver.require([f_initial, f_trans, f_obj_types, f_fresh, f_moving, \
    f_remaining, f_data, f_final])
  t_encode1 = time.perf_counter() - t_start
  return (encoding, t_encode1)


def process(net, log, options):
  object = options["object"]
  skip_existing = options["skip existing"]
  z = options["z"]
  fixed_obj = options["fixed objects"]
  solver = YicesSolver() #
  traces = list(log.split_into_traces())
  print("%d traces" % len(traces))
  traces.sort(key=lambda t: (len(t), len(t.get_objects()), t.smallest_object()))
  trace_selection = traces if object == None else \
    [t for t in traces if object in t.get_objects() ]
  for (i,trace) in enumerate(trace_selection): # A
    if (skip_existing and os.path.exists(file_for_trace(trace))) or \
      (z != None and i % 8 != z):
      print("skip this trace")
      continue
    
    t_start = time.perf_counter()
    print("work on %d" % i)
    solver.push()
    out = "TRACE %d (#events %d, #objects %d)\n" % (i, len(trace), \
      len(trace.get_objects()))
    print(out)
    out += "trace" + str(trace) + "\n"
    (encoding, t_enc1) = create_encoding(solver, trace, net, fixed_obj)
    (dist,t_enc2, t_solve, dec_out) = conformance_check(encoding, log, options)
    out += dec_out
    out += "encoding time: %.2f, solving time %.2f, total time %.2f\n" % \
      (t_enc1 + t_enc2, t_solve, time.perf_counter() - t_start)
    print(out)
    save_result(trace, out)
    solver.pop()
    solver.reset()
    # time.sleep(20)


def process_args(argv):
  usage = "cocomot.py <model_file> <log_file> [-o <object> | -s] [-x]"
  opts = default_options
  try:
    optargs, args = getopt.getopt(argv,"hxfo:v:d:l:n:z:")
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
      opts["skip existing"] = False # for experiments, skip existing results
    elif opt == "-f":
      opts["fixed objects"] = True
    elif opt == "-o":
      opts["object"] = arg
    elif opt == "-v":
      opts["verbose"] = int(arg)
    elif opt == "-n":
      opts["numprocs"] = int(arg)
    elif opt == "-z":
      opts["z"] = int(arg)
  return opts

if __name__ == "__main__":
  ps = process_args(sys.argv[1:])
  net = OPI(read_pnml_input(ps["model"]))
  log = read_ocel(ps["log"])
  process(net, log, ps)

  