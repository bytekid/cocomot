import time 

from smt.z3solver import Z3Solver
from smt.ysolver import YicesSolver
from glocal.cost_schema import CostSchema, parse_cost_schema
from glocal.encoding import GlocalEncoding

def create_encoding(solver, trace_length, dpn, cost_schemas):
  step_bound = trace_length + dpn.shortest_accepted() + 2
  dpn.compute_reachable(step_bound)
  encoding = GlocalEncoding(dpn, solver, step_bound, cost_schemas)

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

def filter_trace(trace, dpn):
  return [ e for e in trace if e["label"] in dpn.get_labels() ]

def get_all_activities(dpns):
  return set([ t["label"] for m in dpns for t in m.transitions() \
    if not t["invisible"]])

def conformance_check_trace(trace, dpns, solver, options):
  cost_schemas = options.cost_schema
  assert(len(cost_schemas) == len(dpns)) # one schema per agent
  activities = get_all_activities(dpns)
  vars = [v["name"] for v in dpns[0].variables()] # assume all DPNs share vars
  cost_schemas = [ parse_cost_schema(c, activities, vars) for c in cost_schemas ]
  encodings = []
  total_cost = solver.num(0)
  for i, (dpn_i, costs_i) in enumerate(zip(dpns, cost_schemas)):
    trace_i = filter_trace(trace, dpn_i)
    # print("trace %d" % i, trace_i)
    encoding_i, t_enc = create_encoding(solver, len(trace_i), dpn_i, costs_i)
    encodings.append(encoding_i)
    (dist_i, dconstr_i) = encoding_i.edit_distance(trace_i, costs_i)
    total_cost = solver.plus(total_cost, dist_i)
    solver.require([dconstr_i])
  
  enum_encodings = enumerate(encodings)
  compatible = [ e1.encode_compatible(e2) \
    for (i,e1) in enum_encodings for (j,e2) in enum_encodings if i < j]
  solver.require(compatible)

  model = solver.minimize(total_cost, 10000)
  if model == None: # timeout
    print("timeout/no model found")
  else:
    distance = model.eval_int(total_cost)
    print("overall cost ", distance)

def conformance_check(log, dpns, options):
  solver = YicesSolver() # Z3Solver() # 
  for t in log:
    solver.push()
    conformance_check_trace(t, dpns, solver, options)
    solver.pop()
    