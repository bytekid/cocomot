from random import random, sample, randint
from math import floor, ceil

from uncertainty.trace import *

def all(traces):
  #add_indeterminacy(traces, prob=0.1)
  #add_uncertain_activities(traces, prob=0.1, num=1)
  #make_timestamps_equal(traces)
  #add_uncertain_timestamps(traces, prob=0.3)
  add_uncertain_discrete_data(traces, prob=0.1, num=2)
  #add_uncertain_continuous_data(traces, prob=0.2)
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


# add with probability prob to trace events uncertainty to data. To that end,
# an already present data variable is chosen randomly, and num data values are
# added; if the present value is v, the added values are in the interval 
# [ v-ratio*v/2, v+ratio*v/2]
# FIXME: restrict generated values to value range that appears in log?
def add_uncertain_discrete_data(traces, prob=0.2, num=1, ratio=0.3):
  assert(num > 0)
  for t in traces:
    for e in t:
      vars = [ x for x in e.data() if e.data_variable(x).kind() != "string" ]
      if random() <= prob and len(vars) > 0:
        x = vars[randint(0, len(vars)-1)]
        xelem = e.data_variable(x)
        xval = float(xelem.admissible()) # assumed to be fixed value
        xlow = xval - xval*ratio/2
        xupp = xval + xval*ratio/2 if xval != 0 else 1
        is_int = xelem.kind() == "int"
        if is_int:
          xlow, xupp = floor(xlow), ceil(xupp)
          num = min(num, xupp-xlow) # one less because xval is already there
        values = [int(xval) if is_int else xval]
        while(len(values) < num + 1):
          v = randint(xlow, xupp) if is_int else rand_range(xlow, xupp)
          if not v in values:
            print("add value", v)
            values.append(v)
        uval = UncertainDataValue(xelem.kind(), x, values=values)
        e.set_data(x, uval)

# add with probability prob to trace events uncertainty to data. To that end,
# a present data variable is chosen randomly. if the present value is v, the 
# added value interval is [ v-ratio*v/2, v+ratio*v/2]
def add_uncertain_continuous_data(traces, prob=0.2, ratio=0.3):
  for t in traces:
    for e in t:
      vars = [ x for x in e.data() if e.data_variable(x).kind() != "string" ]
      if random() <= prob and len(vars) > 0:
        x = vars[randint(0, len(vars)-1)]
        xelem = e.data_variable(x)
        xval = float(xelem.admissible()) # assumed to be fixed value
        xlow, xupp = xval - xval*ratio/2, xval + xval*ratio/2
        is_int = xelem.kind() == "int"
        if is_int:
          xlow, xupp = floor(xlow), ceil(xupp)
        uval = UncertainDataValue(xelem.kind(), x, lower=xlow, upper=xupp)
        e.set_data(x, uval)

