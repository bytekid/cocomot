from cocomot import process_args
import sys
import time
import os

from objectcentric.opi import OPI
from objectcentric.read import ocel as read_ocel
from objectcentric.encoding import Encoding
from dpn.read import read_pnml_input
from smt.ysolver import YicesSolver
from smt.cvc5solver import CVC5Solver
from smt.z3solver import Z3Solver

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
  #for (i,trace) in enumerate(traces[:500]):
  for (i,trace) in enumerate([t for t in traces if "Application_898874076" in t.get_objects() ]): # A
  #for (i,trace) in enumerate([t for t in traces if "Offer_1760956501" in t.get_objects() ]): # B, sb 12: 392.72 without nu, 320 with nu, dist 9
    #if os.path.exists(file_for_trace(trace)):
    #  continue
    
    t_start = time.perf_counter()
    print("work on %d" % i)
    solver.push()
    out = "TRACE %d (#events %d, #objects %d)\n" % (i, len(trace), \
      len(trace.get_objects()))
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

if __name__ == "__main__":
  ps = process_args(sys.argv[1:])
  net = OPI(read_pnml_input(ps["model"]))
  log = read_ocel(ps["log"])
  process(net, log, ps["verbose"])

  