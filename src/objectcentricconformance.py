from cocomot import process_args
import sys
import time

from objectcentric.opi import OPI
from objectcentric.read import ocel as read_ocel
from objectcentric.encoding import Encoding
from dpn.read import read_pnml_input
from smt.ysolver import YicesSolver

def print_trace_distance(trace, t_encode2, t_solve, distance):
  print("distance %d" % distance)

def conformance_check(encoding, trace, verbose):
  t_start = time.perf_counter()
  (dist, dconstr) = encoding.edit_distance()
  t_encode2 = time.perf_counter() - t_start

  encoding.get_solver().require([dconstr])

  model = encoding.get_solver().minimize(dist, encoding.get_step_bound())
  t_solve = encoding.get_solver().t_solve
  if model == None: # timeout
    return (None, None, t_encode2, t_solve)

  distance = model.eval_int(dist)
  alignment_decoded = encoding.decode_alignment(trace, model)
  print_trace_distance(trace, t_encode2, t_solve, distance)

  model.destroy()
  return (distance, alignment_decoded, t_encode2, t_solve)


def create_encoding(solver, trace, net):
  encoding = Encoding(solver, net, trace)
  # encoding parts
  t_start = time.perf_counter()
  f_initial = encoding.initial_state()
  f_object_types = encoding.object_types()
  f_tokens = encoding.token_game()
  f_fresh = encoding.freshness()
  f_final = encoding.final_state()
  encoding.prepare_edit_distance()
  solver.require([f_initial, f_object_types, f_tokens, f_fresh, f_final])
  t_encode1 = time.perf_counter() - t_start
  return (encoding, t_encode1)


def process(net, log, verbose):
  solver = YicesSolver()
  (encoding, t_enc1) = create_encoding(solver, log, net)
  conformance_check(encoding, log, verbose)

if __name__ == "__main__":
  ps = process_args(sys.argv[1:])
  net = OPI(read_pnml_input(ps["model"]))
  log = read_ocel(ps["log"])
  process(net, log, ps["verbose"])

  