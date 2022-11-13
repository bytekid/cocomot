from random import random, sample, randint

from uncertainty.trace import *

def all(traces):
  #add_indeterminacy(traces, prob=0.1)
  #add_uncertain_activities(traces, prob=0.1, num=1)
  #make_timestamps_equal(traces)
  add_uncertain_timestamps(traces, prob=0.3)
  log = UncertainLog(traces)
  xml = log.to_xes()
  print("<?xml version='1.0' encoding='UTF-8'?>")
  print(xml.toprettyxml())


def rand_range(low, high):
  probv = (float(randint(0, 100)) / 100) * (high - low) + low
  return float(int(probv*100))/100 # precision 2 places after comma


# add with probability prob to trace events an indeterminacy value. The value is
# in  ]indet_lower, indet_upper[, with two digits precision 
def add_indeterminacy(traces, prob=0.2, indet_lower=0.1,indet_upper=0.9):
  for t in traces:
    for e in t:
      if random() <= prob:
        e.set_indeterminacy(Indeterminacy(rand_range(indet_lower,indet_upper)))


# add with probability prob to trace events num additional activity labels. The
# probability value of the original labels is in  ]indet_lower, indet_upper[, 
# with two digits precision
def add_uncertain_activities(traces, prob=0.2, num=1, p_lower=0.1, p_upper=0.9):
  assert(num > 0)
  labels = set([ l for t in traces for e in t for l in e.labels()])
  for t in traces:
    for e in t:
      if random() <= prob:
        lab = list(e.labels())[0]
        labels = labels.difference(set([lab])) # other labels
        num_for_trace = min(num, len(labels))
        add = sample(labels, num_for_trace)
        p = rand_range(p_lower, p_upper)
        acts = [(lab, p)] + [ (a, (1-p) / num_for_trace) for a in add ]
        uact = UncertainActivity(dict(acts))
        e.set_uncertain_activity(uact)

# for every trace t, set all events in t to the same uncertain timestamp
# (lower and upper bound are equal)
def make_timestamps_equal(traces):
  for t in traces:
    thetime = t[0].lower_time()
    utime = UncertainTimestamp(thetime, upper=thetime)
    for e in t:
      e.set_uncertain_time(utime)

# add with probability prob to trace events uncertain timestamps, in the following
# sense: the timestamp t is replaced by aduration interval with mid point t; the
#  width of the interval is given by interval_ration*trace_duration, where
# trace_duration is the time difference between the first and the last event
# in the trace.
def add_uncertain_timestamps(traces, prob=0.2, interval_ratio=0.3):
  for t in traces:
    start_time = t[0].lower_time()
    end_time = t[-1].lower_time()
    trace_duration = end_time - start_time
    for e in t:
      if random() <= prob:
        tlow = e.lower_time() - trace_duration / 2
        tupp = e.lower_time() + trace_duration / 2
        e.set_uncertain_time(UncertainTimestamp(tlow, upper=tupp))
