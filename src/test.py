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
  tcnt = 0
  print("%d cocomot tests" % len(tests))
  oks = 0

  for t in tests:
    path = os.path.join(TEST_DIR, t)
    pnmls = [ f for f in os.listdir(path) if "pnml" in f ]
    xess = sorted([ f for f in os.listdir(path) if "xes" in f ])
    if len(pnmls) < 1 or len(xess) < 1: # consider only dirs with pnml and xes
      continue

    dpn = DPN(cocomot.read_pnml_input(os.path.join(path, pnmls[0])))
    for xes in xess:
      # desired distance result is given by the test name, e.g. 0 for test_1_0
      real_distance = float(xes[xes.rfind("_")+1:xes.rfind(".")])
      log, is_uncertain = cocomot.read_log(os.path.join(path, xes))
      trace = log[0] if is_uncertain else cocomot.preprocess_log(log, dpn)[0]
      start = time.time()
      if is_uncertain:
        ukind = "min" if "min" in xes else "fit"
        res = cocomot.cocomot_uncertain(dpn, [trace], ukind, verbose=0)
      else:
        slv = YicesSolver()
        res = cocomot.conformance_check_single_trace(slv, (0,trace,1),dpn,verbose=0)
        slv.destroy()
      duration = time.time() - start
      computed_distance = res[0]
      correct = float(computed_distance) == float(real_distance)
      oks += 1 if correct else 0
      res = "OK" if correct else "FAIL"
      print("    %s/%s %s %s    (%.2f)" % (t, xes, res, real_distance,duration))
      tcnt += 1
  print("%d/%d OK %s"% (oks,tcnt, "" if oks==tcnt else str(tcnt-oks) + " FAIL"))
    
