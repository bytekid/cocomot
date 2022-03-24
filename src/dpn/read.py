import pyparsing as pyp
import json
from xml.dom import minidom
from html import unescape

from dpn.expr import Expr, Num, Var, Charstr, Cmp, BinOp, BinCon

pyp.ParserElement.enablePackrat()

### parsing stuff
def parse_expr(s):
  LPAR = pyp.Literal('(').suppress()
  RPAR = pyp.Literal(')').suppress()
  quote = pyp.Literal('"').suppress()
  sp = pyp.OneOrMore(pyp.White()).suppress()
  sps = pyp.ZeroOrMore(pyp.White()).suppress()
  nums = pyp.Word(pyp.srange("[0-9]"))
  num = (nums + pyp.Optional(pyp.Literal('.') + nums))\
    .setParseAction(lambda toks: Num(''.join(toks)))
  var = (pyp.Word(pyp.alphas.lower(), pyp.srange("[a-zA-Z0-9]")) + pyp.Optional(pyp.Literal("'"))).\
    setParseAction(lambda toks: Var(toks[0], toks[1] if len(toks) > 1 else None))
  chars = (pyp.QuotedString('"')).setParseAction(lambda toks: Charstr(toks[0]))
  boolean = (pyp.oneOf("True False true false")).setParseAction(lambda toks: Bool(toks[0]))
  term = pyp.Forward()
  pterm = (LPAR + sps + term + sps + RPAR).setParseAction(lambda toks: toks[0])
  term << pyp.infixNotation(num | var | pterm | chars | boolean, [
        (pyp.oneOf("+ -"), 2, pyp.opAssoc.LEFT, lambda ts: BinOp(ts[0][0], ts[0][1], ts[0][2])),
    ])

  formula = pyp.Forward()
  cmpop = pyp.oneOf("== < > <= >= !=")
  atom = (sps + term + sps + cmpop + sps + term + sps).\
     setParseAction(lambda toks: Cmp(toks[1], toks[0], toks[2]))
  patom = (LPAR + sps + atom + sps + RPAR).setParseAction(lambda toks: toks[0])
  formula << pyp.infixNotation(patom, [
        (pyp.oneOf("&& ||"), 2, pyp.opAssoc.LEFT, lambda ts: BinCon(ts[0][0], ts[0][1], ts[0][2])),
    ])
  res = formula.parseString(s)
  r = res[0] if len(res) > 0 else None
  return r


def read_json_input(jsonfile):
  file = open(jsonfile, "r")
  content = file.read()
  input = json.loads(content)
  for t in input["model"]["transitions"]:
    if "condition" in t:
      t["constraint"] = parse_expr(t["condition"])
  return input

def base_var(name):
  return name[:-1] if name[-1] == '\'' else name

def read_pnml_input(pnmlfile):
  dom = minidom.parse(pnmlfile)
  dpn = {
    "variables"         :[],
    "places"            :[],
    "transitions"       :[],
    "arcs"              :[]
  }
    
  # arcs
  for a in dom.getElementsByTagName('arc'):
    src = a.getAttribute('source')
    tgt = a.getAttribute('target')
    id = a.getAttribute('id')
    # arctype = a.getElementsByTagName('arctype')[0]
    # t = arctype.getElementsByTagName('text')[0].firstChild.nodeValue
    dpn["arcs"].append({ "source": src, "target": tgt, "id": id })
  
  # transitions
  for a in dom.getElementsByTagName('transition'):
    id = a.getAttribute('id')
    inv = a.getAttribute('invisible')
    inv = True if inv == 'true' else False
    guard = unescape(a.getAttribute('guard'))
    n = a.getElementsByTagName('name')[0]
    nameval = n.getElementsByTagName('text')[0].firstChild.nodeValue
    ws = [w.firstChild.nodeValue for w in a.getElementsByTagName('writeVariable')]
    t = { "id": id, "label": nameval, "write": ws, "invisible": inv}
    if guard:
      t["constraint"] = parse_expr(guard)
    dpn["transitions"].append(t)

  # places
  for a in dom.getElementsByTagName('page')[0].getElementsByTagName('place'):
    id = a.getAttribute('id')
    p = { "id": id }
    name = a.getElementsByTagName('name')
    if name:
      p["name"] = name[0].getElementsByTagName('text')[0].firstChild.nodeValue
    final = a.getElementsByTagName('finalMarking')
    if len(final) > 0:
      p["final"] = int(final[0].getElementsByTagName('text')[0].firstChild.nodeValue)
    init = a.getElementsByTagName('initialMarking')
    if len(init) > 0:
      p["initial"] = int(init[0].getElementsByTagName('text')[0].firstChild.nodeValue)
    dpn["places"].append(p)
  
  # variables
  varlist = dom.getElementsByTagName('variable')
  # determine variables used in guards
  guard_vars = set([])
  for t in dpn["transitions"]:
    if "constraint" in t:
      guard_vars = guard_vars.union([base_var(v) for v in t["constraint"].vars()])
  
  for v in varlist:
    name = v.getElementsByTagName('name')[0].firstChild.nodeValue
    if name in guard_vars:
      vtype = v.getAttribute('type')
      var = {"name": name, "initialValue": 0, "type": vtype}
      dpn["variables"].append(var)
  
  for t in dpn["transitions"]:
    if "guard" in t:
      guard = t["guard"]
      assert(set([v for v in vs if v+"'" in guard ]).issubset(set(t["write"])))

    # in case finalmarkings are given separately
    final = dom.getElementsByTagName('net')[0].getElementsByTagName('finalmarkings')
    for i in range(0, len(final)):
      if len(final[i].getElementsByTagName('place')) > 0:
        place = final[i].getElementsByTagName('place')[0]
        id = place.getAttribute('idref')
        count = int(place.getElementsByTagName('text')[0].firstChild.nodeValue)
        if count > 0:
          for p in dpn["places"]:
            if p["id"] == id:
              p["final"] = count
              break

  return dpn