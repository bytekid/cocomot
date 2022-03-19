import sys
import time
import multiprocessing
from pm4py.objects.log.importer.xes import importer as xes_importer
from pm4py.objects.log.exporter.xes import exporter as xes_exporter
import json
import getopt
import pm4py
import os
import subprocess
import re

from cocomot import *

def preprocess_log(log, dpn):
  log_processed = []
  for trace in log:
    log_processed.append((trace, preprocess_trace(trace, dpn)))
  return log_processed

def split():
  ps = process_args(sys.argv[1:])
  dpn = DPN(read_pnml_input(ps["model"]))
  (log, has_uncertainty) = read_log(ps["log"])
  print("number of traces: %d" % len(log))

  #naive_part = NaivePartitioning(list(logd.values()))
  #interval_part = IntervalPartitioning(dpn, naive_part.representatives())

  i = 0
  ts = []
  for t in log:
    tp = preprocess_trace(t, dpn)
    if not tp in ts:
      log1 = pm4py.filter_log(lambda x: x == t, log)
      print(len(log1), i)
      xes_exporter.apply(log1, 'data/hospital_billing/single_traces/' + str(i) + '.xes')
      i += 1
      ts.append(tp)

def check(job):
  model = job["m"]
  log = job["l"]
  timeout_interval = job["t"]
  cmd = "python3 cocomot.py -m %s -l %s" % (model, log)
  cmd = ("./sandbox %d %s" % (timeout_interval, cmd))
  #print(cmd)
  process = subprocess.Popen(cmd.split(), stdout=subprocess.PIPE)
  out, err = process.communicate()
  if err:
    print(err)

  if "TIMEOUT" in str(out):
    m = re.search("length (\d+)", str(out))
    len = int(m.groups()[0]) if m else 0
    (dist, tenc, tsol) = (0,0,0)
    res = "TIMEOUT"
  else:
    m = re.search("length (\d+).*DISTANCE : (\d+).*time/encode: (\d+.\d+)\s*time/solve: (\d+.\d+)", str(out))
    if m:
      len = int(m.groups()[0])
      dist = int(m.groups()[1])
      tenc = float(m.groups()[2])
      tsol = float(m.groups()[3])
    res = "SUCCESS"
  return (res, len, dist, tenc, tsol)


if __name__ == "__main__":
  ps = process_args(sys.argv[1:])
  dpn = DPN(read_pnml_input(ps["model"]))

  jobs = []
  TIMEOUT = 5
  for filename in os.listdir(ps["log"]):
    f = os.path.join(ps["log"],filename)
    if "xes" in filename:
        jobs.append({"m": ps["model"], "l": f, "t": TIMEOUT})
      
  pool = multiprocessing.Pool(ps["numprocs"])
  results = pool.map_async(check, jobs[:5])
  pool.close()
  pool.join()
  for (res, length, dist, tenc, tsol) in results.get():
    print("%s, %d, %d, %.2f, %.2f" % (res, length, dist, tenc, tsol))
