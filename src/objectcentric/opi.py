from sys import maxsize
import xml.dom.minidom
from copy import deepcopy

from utils import VarType
from dpn.dpn import DPN

# object-centric petri nets with identifiers
class OPI(DPN):

  def __init__(self, opi_as_array):
    super().__init__(opi_as_array)

  def step_bound(self, trace):
    return len(trace) + self.shortest_accepted()

  def object_bound(self, trace):
    return len(trace.objects())