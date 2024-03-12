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
  activities = set([ t["label"] for t in dpn.transitions ])
  return [ e for e in trace if e["label"] in activities ]

def conformance_check(trace, dpns, solver, options):
  cost_schemas = options.cost_schemas
  assert(len(cost_schemas) == len(dpns)) # one schema per agent
  cost_schemas = [ CostSchema(c) for c in cost_schemas ]
  encodings = []
  total_cost = solver.num(0)
  for (dpn_i, costs_i) in zip(dpns, cost_schemas):
    trace_i = filter_trace(trace, dpn)
    encoding_i = create_encoding(solver, len(trace_i), dpn_i, costs_i)
    encodings.append(encoding_i)
    (dist_i, dconstr_i) = encoding_i.edit_distance(trace_i)
    total_cost = solver.plus(total_cost, dist_i)
    solver.require([dconstr_i])
  
  # FIXME compatibility

  max_step_bound = max([ e.step_bound() for e in encodings ])
  model = solver.minimize(total_cost, max_step_bound)
  if model == None: # timeout
    print(timeout)

  distance = model.eval_int(total_cost)

def conformance_check_log(log, dpns, options):
  solver = Z3Solver()
  for t in log:
    solver.push()
    conformance_check(t, dpns, solver, options)
    solver.pop()
    