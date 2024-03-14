import pyparsing as pyp
from functools import reduce

from dpn.expr import Expr, Num, Var, Charstr, Cmp, BinOp, BinCon

class Pattern:
  def __init__(self, regex, activity, cost):
    self._regex = regex
    self._activity = activity
    self._cost = cost
  
  def __str__(self):
    return "(%s, %s, %s)" % \
      (str(self._regex), str(self._activity), self._cost)

class CostSchema:
  def __init__(self, log_patterns, mod_patterns, default, symbols):
    self._log_patterns = log_patterns
    self._mod_patterns = mod_patterns
    self._default = default
    self._symbols = symbols
    print("create cost schema", str(self))

  def __str__(self):
    join = lambda ss: \
      reduce(lambda a,s: a+(", " if len(a) > 0 else "")+str(s),ss,"[") + "]"
    return "(%s, %s, %d)" % \
      (join(self._log_patterns), join(self._mod_patterns), self._default)

  def get_patterns(self):
    return (self._log_patterns, self._mod_patterns, self._default)

def parse_cost_schema(s, activities, vars):
  symbols = {}
  def addActivitySymbol(ts):
    c = chr(len(symbols) + 65)
    act = ts[0]
    constr = ts[1] if len(ts) > 1 else None
    key = act + (constr if constr else "")
    if key in symbols:
      return symbols[key][0]
    else:
      symbols[key] = (c, ts[0], ts[1] if len(ts) > 1 else None)
      return c

  def concatAll(ts):
    #print("concat all", ts)
    sts = [ t if isinstance(t,str) else concatAll(t) for t in ts ]
    return reduce(lambda a,s: a + s, sts)

  LPAR = pyp.Literal('(').suppress()
  RPAR = pyp.Literal(')').suppress()
  LPARV = pyp.Literal('(')
  RPARV = pyp.Literal(')')
  LBRACK = pyp.Literal('[').suppress()
  RBRACK = pyp.Literal(']').suppress()
  LCBRAC = pyp.Literal('{').suppress()
  RCBRAC = pyp.Literal('}').suppress()
  COMMA = pyp.Literal(',').suppress()

  var_list = reduce(lambda acc,s: acc + " " +s, vars, "")
  nums = pyp.Word(pyp.srange("[0-9]"))
  num = (nums + pyp.Optional(pyp.Literal('.') + nums))\
    .setParseAction(lambda toks: Num(''.join(toks)))
  var = (pyp.oneOf(var_list)).\
    setParseAction(lambda toks: Var(toks[0], toks[1] if len(toks) > 1 else None))
  boolean = (pyp.oneOf("True False true false")).setParseAction(lambda toks: Bool(toks[0]))
  term = pyp.Forward()
  pterm = (LPAR + term + RPAR).setParseAction(lambda toks: toks[0])
  term << pyp.infixNotation(num | var | pterm | boolean, [
        (pyp.oneOf("+ -"), 2, pyp.opAssoc.LEFT, lambda ts: BinOp(ts[0][0], ts[0][1], ts[0][2])),
    ])
  formula = pyp.Forward()
  cmpop = pyp.oneOf("== < > <= >= !=")
  atom = (term + cmpop + term).\
     setParseAction(lambda toks: Cmp(toks[1], toks[0], toks[2]))
  patom = (LPAR + atom + RPAR).setParseAction(lambda toks: toks[0])
  formula << pyp.infixNotation(patom, [
        (pyp.oneOf("&& ||"), 2, pyp.opAssoc.LEFT, lambda ts: BinCon(ts[0][0], ts[0][1], ts[0][2])),
    ])

  activity_list = reduce(lambda acc,s: acc + " " +s, activities, "")[1:]
  activity = (pyp.oneOf(activity_list) + pyp.Optional(LCBRAC + formula + RCBRAC )) \
    .setParseAction(addActivitySymbol)
  regex = pyp.Forward()
  DUMMY = pyp.Literal("_DUMMY").suppress()
  regex << pyp.infixNotation(activity | pyp.Literal(".") | DUMMY, [
        ("*", 2, pyp.opAssoc.RIGHT, concatAll), # hack
        (None, 2, pyp.opAssoc.LEFT, concatAll),
        ("+", 2, pyp.opAssoc.LEFT, concatAll)
    ], lpar=pyp.Literal("("), rpar=pyp.Literal(")"))

  pattern = (LPAR + regex + COMMA + activity + COMMA + nums + RPAR) \
    .setParseAction(lambda ts: Pattern(ts[0], ts[1], ts[2]))
  pattern_list = (LBRACK + pyp.DelimitedList(pattern, delim=COMMA) + RBRACK) \
    .setParseAction(lambda ts: [ts]) | \
    (LBRACK + RBRACK).setParseAction(lambda _: [[]])
  schema = (LPAR + pattern_list + COMMA + pattern_list + COMMA + nums + RPAR) \
    .setParseAction(lambda ts: CostSchema(ts[0], ts[1], int(ts[2]), symbols))
  # print("parsing", s)
  cost_schema = schema.parseString(s.replace("*", "*_DUMMY"))
  return cost_schema[0] # get first element of ParseResults