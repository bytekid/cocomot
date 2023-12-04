import sys
import time
import os
import getopt

from objectcentric.opi import OPI
from objectcentric.read import ocel as read_ocel
from objectcentric.encoding import Encoding
from dpn.read import read_pnml_input
from smt.ysolver import YicesSolver
from smt.cvc5solver import CVC5Solver
from smt.z3solver import Z3Solver

default_options = {
    "anti": None,   # use anti-alignments
    "json": False,  # output alignments as json
    "log": None,    # log file to be used
    "many": None,   # use multi-alignments
    "model": None,  # model input (DPN) 
    "multi": None,  # use multi-alignments
    "numprocs": 1,  # number of processsors to use in parallel
    "obfuscate": None, # make given log uncertain
    "realizations": False, # compute realizations of uncertain log
    "solver": None, # could be yices, z3, z3-inc, om, om-inc
    "uncertainty": None, # use conformance checking with uncertainty
    "verbose": 1, # verbosity of output
    "y": None, # debugging
    "z": None # debugging
  }

def file_for_trace(trace):
  return "out/" + trace.smallest_object() + ".txt"

def save_result(trace, content):
  f = open(file_for_trace(trace), "w")
  f.write(content)
  f.close()

def conformance_check(encoding, trace, verbose):
  t_start = time.perf_counter()
  (dist, dconstr) = encoding.edit_distance()
  t_encode2 = time.perf_counter() - t_start

  encoding.get_solver().require([encoding.cache_constraints()])
  encoding.get_solver().require([dconstr])

  model = encoding.get_solver().minimize(dist, max=encoding.get_step_bound())
  #model = encoding.get_solver().check_sat(encoding.get_solver().true())
  t_solve = encoding.get_solver().t_solve
  if model == None: # timeout or bug
    print("no model found")
    return (None, None, t_encode2, t_solve)

  distance = model.eval_int(dist)
  out = encoding.decode(model)
  out += "distance %d\n" % distance

  model.destroy()
  return (distance, t_encode2, t_solve, out)


def create_encoding(solver, trace, net):
  net.reset()
  encoding = Encoding(solver, net, trace)
  t_start = time.perf_counter()
  encoding.create_variables()
  f_initial = encoding.initial_state()
  f_trans = encoding.transition_range()
  f_obj_types = encoding.object_types()
  f_moving = encoding.moving_tokens()
  f_remaining = encoding.remaining_tokens()
  f_fresh = encoding.freshness()
  f_final = encoding.final_state()
  solver.require([f_initial, f_trans, f_obj_types, f_fresh, f_moving, \
    f_remaining, f_final])
  t_encode1 = time.perf_counter() - t_start
  return (encoding, t_encode1)


def process(net, log, verbose):
  solver = YicesSolver() #Z3Solver() #  
  traces = list(log.split_into_traces())
  print("%d traces" % len(traces))
  traces.sort(key=lambda t: (len(t), len(t.get_objects()), t.smallest_object()))
  for (i,trace) in enumerate(traces[:400]):
  #for (i,trace) in enumerate([t for t in traces if "Application_299646442" in t.get_objects() ]): # A
    if os.path.exists(file_for_trace(trace)):
      continue
    
    t_start = time.perf_counter()
    print("work on %d" % i)
    solver.push()
    out = "TRACE %d (#events %d, #objects %d)\n" % (i, len(trace), \
      len(trace.get_objects()))
    print(out)
    out += "trace" + str(trace) + "\n"
    (encoding, t_enc1) = create_encoding(solver, trace, net)
    (dist,t_enc2, t_solve, dec_out) = conformance_check(encoding, log, verbose)
    out += dec_out
    out += "encoding time: %.2f, solving time %.2f, total time %.2f\n" % \
      (t_enc1 + t_enc2, t_solve, time.perf_counter() - t_start)
    print(out)
    save_result(trace, out)
    solver.pop()
    solver.reset()


def process_args(argv):
  usage = "cocomot.py <model_file> <log_file> [-p <property_string> | -s] [-x <number>]"
  opts = default_options
  try:
    optargs, args = getopt.getopt(argv,"hjmro:u:v:d:l:n:x:a:s:z:y:")
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
      if arg not in ["like", "real"]:
        print(usage)
        sys.exit(1)
      opts["uncertainty"] = arg
    elif opt == "-m":
      opts["multi"] = True
    elif opt == "-r":
      opts["realizations"] = True
    elif opt == "-j":
      opts["json"] = True
      opts["verbose"] = 0
    elif opt == "-a":
      opts["anti"] = int(arg)
    elif opt == "-z":
      opts["z"] = int(arg)
    elif opt == "-y":
      opts["y"] = int(arg)
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
  net = OPI(read_pnml_input(ps["model"]))
  log = read_ocel(ps["log"])
  process(net, log, ps["verbose"])

  