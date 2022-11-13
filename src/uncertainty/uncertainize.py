from random import random, sample

from uncertainty.trace import *

def all(traces):
  add_indeterminacy(traces, prob=0.1)
  add_uncertain_activities(traces, prob=0.1, num=1)
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
