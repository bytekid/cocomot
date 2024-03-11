class Options:
  anti = False        # check anti-alignments
  cost_schema =  None # for glocal conformance
  json = False        # output alignments as json
  glocal = False      # whether glocal conformance is checked
  log = None          # log file to be used
  many = None         # optimization, check multiple traces of same length at once
  model = None        # model input (DPN) 
  multi = False       # use multi-alignments
  numprocs = 1        # number of processsors to use in parallel
  obfuscate = None    # make given log uncertain
  compute_realizations = False # compute realizations of uncertain log
  solver = None       # could be yices, z3, z3-inc, om, om-inc
  uncertainty = None  # use conformance checking with uncertainty
  verbose = 1         # verbosity of output
  z = None            # debugging

  def __init__(self):
    pass

  def __str__(self):
    return "[anti=%s, " % str(self.anti) + \
      "cost schema=%s, " % str(self.cost_schema) + \
      "json=%s, " % str(self.json) + \
      "glocal=%s, " % str(self.glocal) + \
      "log=%s, " % str(self.log) + \
      "many=%s, " % str(self.many) + \
      "model=%s, " % str(self.model) + \
      "multi=%s, " % str(self.multi) + \
      "numprocs=%s, " % str(self.numprocs) + \
      "obfuscate=%s, " % str(self.obfuscate) + \
      "compute realizations=%s, " % str(self.compute_realizations) + \
      "solver=%s, " % str(self.solver) + \
      "uncertainty=%s, " % str(self.uncertainty) + \
      "verbose=%s, " % str(self.verbose) + \
      "z=%s]" % str(self.z)
