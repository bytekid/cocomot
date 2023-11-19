class Trace:
  def __init__(self, events, ordering, objects):
    self._events = events
    self._ordering = ordering
    self._objects = objects

  def get_objects(self):
    return self._objects

  def get_events(self):
    return self._events

  def get_ordering(self):
    return self._ordering

  def __len__(self):
    return len(self._events)


class Log:
  def __init__(self, events, ordering, objects):
    self._events = events
    self._ordering = ordering
    self._objects = objects

  def split_into_traces(self):
    pass # TODO

