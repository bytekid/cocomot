
def spaces(n):
  return "" if n <= 0 else " " + spaces(n-1) 


def pad_to(s, n):
  return s + spaces(n - len(s)) if len(s) < n else s[:n]

class VarType:
  bool = 1
  int = 2
  rat = 3
  real = 4
  string = 5

  def from_str(t):
    map_type = {
      "bool": VarType.bool,
      "int": VarType.int,
      "rat": VarType.rat,
      "real": VarType.real,
      "string": VarType.string,
    }
    return map_type[t]

  def to_str(t):
    if t == VarType.bool:
      return "bool"
    if t == VarType.int:
      return "int"
    if t == VarType.rat:
      return "rat" 
    if t == VarType.string:
      return "string" 
    return "real"

  def to_java(t):
    if t == VarType.bool:
      return "java.lang.Boolean"
    if t == VarType.int:
      return "java.lang.Integer"
    if t == VarType.rat:
      return "java.lang.Double" 
    if t == VarType.string:
      return "java.lang.String" 
    return "java.lang.Double"

  def from_java(t):
    map_java_type = {
      "java.lang.Boolean": VarType.bool,
      "java.lang.Integer": VarType.int,
      "java.lang.Long"   : VarType.int,
      "java.lang.Double" : VarType.real,
      "java.lang.String" : VarType.string,
      "Integer": VarType.int,
      "Rational" : VarType.real,
      "Real" : VarType.real
    }
    return map_java_type[t]
  
def val_type(val):
  vtype = VarType.bool if isinstance(val, bool) else \
    VarType.int if isinstance(val, int) else \
    VarType.real if isinstance(val, float) else VarType.string
  return vtype