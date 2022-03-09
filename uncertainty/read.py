from xml.dom import minidom
from html import unescape

from uncertainty.trace import *

ACTIVITY_KEY = "concept:name"
TIMESTAMP_KEY = "time:timestamp"

def xes(logfile):
  children = \
    lambda d: [c for c in d.childNodes if c.nodeType == c.ELEMENT_NODE]

  dom = minidom.parse(logfile)
  log = []
  for dom_trace in dom.getElementsByTagName('trace'):
    trace = []
    for dom_event in dom_trace.getElementsByTagName('event'):
      indet = Indeterminacy(1)
      activity = None
      time_lower = None
      time_upper = None
      data = []
      for child in children(dom_event):
        key = child.getAttribute('key')
        if key == ACTIVITY_KEY:
          activity = UncertainActivity(child.getAttribute('value'))
        elif key == "time:timestamp":
          time_lower = child.getAttribute('value')
        elif key == "uncertainty:time:timestamp_max":
          time_upper = child.getAttribute('value')
        elif key == "uncertainty:entry":
          indet_data = children(child)
          for d in indet_data:
            if d.getAttribute('key') == "uncertainty:probability":
              indet = Indeterminacy(float(d.getAttribute('value')))
        elif key == "uncertainty:discrete_weak":
          values = children(child)[0]
          # data or concept:name
          acts = {}
          data_values = []
          data_name = None
          for e in children(values):
            ekey = e.getAttribute('key')
            if ekey == "uncertainty:entry": # activities
              activity = None
              probability = None
              for ee in children(e):
                if ee.getAttribute('key') == "concept:name":
                  activity = ee.getAttribute('value')
                if ee.getAttribute('key') == "uncertainty:probability":
                  probability = ee.getAttribute('value')
              acts[activity] = probability
            else: # data
              data_name = ekey
              data_values.append(e.getAttribute('value'))
          if len(acts) > 0:
            activity = UncertainActivity(acts)
          if len(data_values) > 0:
            data.append(UncertainDataValue(data_name, data_values))
            
      time = UncertainTimestamp(time_lower, time_upper)
      event = UncertainEvent(indet, activity, time, data)
      trace.append(event)
    log.append(UncertainTrace(trace))
  return log
