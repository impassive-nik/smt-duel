import z3
from enum import Enum
from parser import prefix_notation

class TurnResult(Enum):
  SUCCESS = 1
  MISTAKE = 2
  LOST = 3
  DRAW = 4

class TurnInfo:
  result = TurnResult.SUCCESS
  debug = ""
  info = ""

  def __init__(self, result, debug = "", info = ""):
    self.result = result
    self.debug = debug
    self.info = info

class SMTSolver:
  variables = ["x", "y", "z"]

  def reset(self):
    self.solver = z3.Solver()
    self.solver.set(unsat_core=True)
    self.solver.from_string("\n".join([("(declare-fun " + x + " () Int)") for x in self.variables]))
  
  def turn(self, inp):
    parsed_input = ""
    try:
      parsed_input = prefix_notation(inp, self.variables)
    except ValueError as e:
      return TurnInfo(TurnResult.MISTAKE, "", str(e))
    
    try:
      self.solver.from_string("(assert " + parsed_input + ")")
    except z3.Z3Exception as e:
      return TurnInfo(TurnResult.MISTAKE, parsed_input, str(e))

    check_result = self.solver.check()
    if check_result == z3.unsat:
      return TurnInfo(TurnResult.LOST, parsed_input)

    if check_result == z3.unknown:
      return TurnInfo(TurnResult.DRAW, parsed_input)
    
    return TurnInfo(TurnResult.SUCCESS, parsed_input)

  def get_variables():
    return self.variables

  def get_operations():
    return unary_ops + binary_ops
