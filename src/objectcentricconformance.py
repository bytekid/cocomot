from cocomot import process_args
import sys
import time

from objectcentric.opi import OPI
from objectcentric.read import ocel as read_ocel
from objectcentric.encoding import Encoding
from dpn.read import read_pnml_input
from smt.ysolver import YicesSolver
from smt.cvc5solver import CVC5Solver
from smt.z3solver import Z3Solver

def print_trace_distance(trace, t_encode2, t_solve, distance):
  print("distance %d" % distance)

def conformance_check(encoding, trace, verbose):
  t_start = time.perf_counter()
  (dist, dconstr) = encoding.edit_distance()
  t_encode2 = time.perf_counter() - t_start

  encoding.get_solver().require([encoding.cache_constraints()])
  encoding.get_solver().require([dconstr])

  model = encoding.get_solver().minimize(dist, encoding.get_step_bound())
  t_solve = encoding.get_solver().t_solve
  if model == None: # timeout or bug
    print("no model found")
    return (None, None, t_encode2, t_solve)

  distance = model.eval_int(dist)
  alignment_decoded = encoding.decode(model)
  print_trace_distance(trace, t_encode2, t_solve, distance)

  model.destroy()
  return (distance, alignment_decoded, t_encode2, t_solve)


def create_encoding(solver, trace, net):
  encoding = Encoding(solver, net, trace)
  # encoding parts
  t_start = time.perf_counter()
  encoding.create_variables()
  f_initial = encoding.initial_state()
  f_trans = encoding.transition_range()
  f_obj_types = encoding.object_types()
  f_moving = encoding.moving_tokens()
  f_remaining = encoding.remaining_tokens()
  f_fresh = encoding.freshness()
  f_final = encoding.final_state()
  solver.require([f_initial, f_trans, f_obj_types, f_fresh, f_moving, f_remaining, f_final])
  t_encode1 = time.perf_counter() - t_start
  return (encoding, t_encode1)


def process(net, log, verbose):
  solver = YicesSolver() # Z3Solver() #  
  (encoding, t_enc1) = create_encoding(solver, log, net)
  (dist, alignment, t_enc2, t_solve) = conformance_check(encoding, log, verbose)
  print("encoding time: %.2f, solving time %.2f" % (t_enc1 + t_enc2, t_solve))

if __name__ == "__main__":
  ps = process_args(sys.argv[1:])
  net = OPI(read_pnml_input(ps["model"]))
  log = read_ocel(ps["log"])
  process(net, log, ps["verbose"])

  