from xml.dom import minidom
from html import unescape
from datetime import datetime

from uncertainty.trace import *

ACTIVITY_KEY = "concept:name"
TIMESTAMP_KEY = "time:timestamp"

def parse_time(timestr):
  try:
    dateformat="%Y-%m-%dT%H:%M:%S%z" # 2000-05-06T00:00:00+02:00
    return datetime.strptime(timestr, dateformat)
  except:
    dateformat="%Y-%m-%dT%H:%M:%S.%z" # 2021-04-26T18:46:40.050+00:00
    return datetime.fromisoformat(timestr)


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
          time_lower = parse_time(child.getAttribute('value'))
        elif key == "uncertainty:time:timestamp_max":
          time_upper = parse_time(child.getAttribute('value'))
        elif key == "uncertainty:entry":
          indet_data = children(child)
          for d in indet_data:
            if d.getAttribute('key') == "uncertainty:probability":
              indet = Indeterminacy(float(d.getAttribute('value')))
        elif key == "uncertainty:discrete_weak": # uncertain activities
          values = children(child)[0]
          acts = {}
          for e in children(values):
            ekey = e.getAttribute('key')
            assert(ekey == "uncertainty:entry")
            for ee in children(e):
              if ee.getAttribute('key') == "concept:name":
                activity = ee.getAttribute('value')
              if ee.getAttribute('key') == "uncertainty:probability":
                probability = ee.getAttribute('value')
            acts[activity] = probability
          activity = UncertainActivity(acts)
        elif key == "uncertainty:discrete_strong": # uncertain data, value set
          xvaluelist = children(child)[0]
          values = []
          data_name = None
          data_type = None
          for e in children(xvaluelist):
            assert(not data_name or data_name == e.getAttribute('key'))
            assert(not data_type or data_type == e.tagName)
            data_type = e.tagName
            data_name = e.getAttribute('key')
            values.append(e.getAttribute('value'))
          data.append(UncertainDataValue(data_type, data_name, values=values))
        elif key == "uncertainty:continuous_strong": # uncertain data, interval
          for e in children(child):
            xbound = children(e)[0]
            if e.getAttribute('key') == "uncertainty:lower:bound":
              l = xbound.getAttribute("value")
            else:
              assert(e.getAttribute('key') == "uncertainty:upper:bound")
              u = xbound.getAttribute("value")
            data_type = xbound.tagName
            data_name = xbound.getAttribute('key')
          assert(l != None and u != None and data_type and data_name)
          data.append(UncertainDataValue(data_type, data_name,lower=l,upper=u))
        else: # data without uncertainty
          name = child.getAttribute('key')
          val = child.getAttribute('value')
          kind = child.tagName
          data.append(UncertainDataValue(kind, key, values = [val] ))

            
      time = UncertainTimestamp(time_lower, time_upper)
      event = UncertainEvent(indet, activity, time, data)
      trace.append(event)
      utrace = UncertainTrace(trace)
    log.append(utrace)
  return log
