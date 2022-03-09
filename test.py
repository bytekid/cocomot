import os
import sys
import time

import cocomot
from dpn.dpn import *
from smt.ysolver import YicesSolver

TEST_DIR = "tests"
PREFIX = "test"

if __name__ == "__main__":
  tests = sorted([ d for d in os.listdir(TEST_DIR) if PREFIX in d ])
  tcnt = len(tests)
  print("%d cocomot tests" % tcnt)
  oks = 0

  for t in tests:
    path = os.path.join(TEST_DIR, t)
    pnmls = [ f for f in os.listdir(path) if "pnml" in f ]
    xess = [ f for f in os.listdir(path) if "xes" in f ]
    if len(pnmls) < 1 or len(xess) < 1: # consider only dirs with pnml and xes
      continue
    
    # the desired distance result is given by the test name, e.g. 0 for test_1_0
    desired_distance = int(t[t.rfind("_")+1:])

    dpn = DPN(cocomot.read_pnml_input(os.path.join(path, pnmls[0])))
    log = cocomot.read_log(os.path.join(path, xess[0]))
    traces = cocomot.preprocess_log(log, dpn)
    solver = YicesSolver()
    trace = (0,traces[0],1)
    start = time.time()
    res = cocomot.conformance_check_single_trace(solver, trace, dpn, verbosity=0)
    end = time.time()
    computed_distance = res[0]
    if computed_distance == desired_distance:
      print("    %s %s OK    (%.2f)" % (t, computed_distance, end - start))
      oks += 1
    else:
      print("    %s %s FAIL  (%.2f)" % (t, computed_distance, end - start))
    
  print("%d/%d OK %s"% (oks,tcnt, "" if oks==tcnt else str(tcnt-oks) + " FAIL"))
    
