import z3
import ast
import re
import io
import tokenize
from enum import Enum
from bot import MathBot

class TurnResult(Enum):
  SUCCESS = 1
  MISTAKE = 2
  TAUTOLOGY = 3 
  LOST = 4
  DRAW = 5

class TurnInfo:
  result = TurnResult.SUCCESS
  debug = ""
  info = ""

  def __init__(self, result, debug = "", info = ""):
    self.result = result
    self.debug = debug
    self.info = info

class ASTVisitor:
  def __init__(self, variables, var_type = "integer"):
    self.variables = variables
    self.var_type = var_type
    self.divisors = []
  
  def str_node(self, node):
    if isinstance(node, ast.AST):
      fields = [(name, self.str_node(val)) for name, val in ast.iter_fields(node) if name not in ('left', 'right')]
      rv = '%s(%s' % (node.__class__.__name__, ', '.join('%s=%s' % field for field in fields))
      return rv + ')'
    else:
      return repr(node)

  def visit_node(self, node, level=0):
    #print(" " * level, self.str_node(node))
    if isinstance(node, ast.Name):
      if not node.id in self.variables:
        raise ValueError("Unknown variable: {}".format(node.id))
      return self.variables[node.id]
    
    if isinstance(node, ast.Constant):
      if self.var_type == "real" and isinstance(node.value, float):
        return z3.RealVal(node.value)
      elif isinstance(node.value, int):
        return z3.IntVal(node.value)
      raise ValueError("Expected integer: {}".format(node.value))

    ops = []
    for field, value in ast.iter_fields(node):
      if field in ('op', 'ops'):
        continue
      if isinstance(value, list):
        for item in value:
          if isinstance(item, ast.AST):
            ops.append(self.visit_node(item, level=level+1))
      elif isinstance(value, ast.AST):
        ops.append(self.visit_node(value, level=level+1))
    
    op_len = len(ops)
    if isinstance(node, ast.BinOp) and op_len == 2:
      if isinstance(node.op, ast.Add):
        return ops[0] + ops[1]
      if isinstance(node.op, ast.Sub):
        return ops[0] - ops[1]
      if isinstance(node.op, ast.Mult):
        return ops[0] * ops[1]
      if isinstance(node.op, ast.Div):
        self.divisors.append(ops[1])
        return ops[0] / ops[1]
      if isinstance(node.op, ast.Mod):
        if self.var_type == "real":
          raise ValueError("Operator '%' can be used in integer arithmetics only!")
        else:
          self.divisors.append(ops[1])
          return ops[0] % ops[1]
      raise ValueError("Unsupported binary operator: {}".format(type(node.op).__name__))

    if isinstance(node, ast.UnaryOp) and op_len == 1:
      if isinstance(node.op, ast.Not):
        return z3.Not(ops[0])
      if isinstance(node.op, ast.USub):
        return -ops[0]
      raise ValueError("Unsupported unary operator: {}".format(type(node.op).__name__))

    if isinstance(node, ast.BoolOp):
      if isinstance(node.op, ast.And) and op_len > 1:
        cur_expr = ops[0]
        for op in ops[1:]:
          cur_expr = z3.And(cur_expr, op)
        return cur_expr
      if isinstance(node.op, ast.Or):
        cur_expr = ops[0]
        for op in ops[1:]:
          cur_expr = z3.Or(cur_expr, op)
        return cur_expr
      raise ValueError("Unsupported boolean operator: {} with {} operands".format(type(node.op).__name__, op_len))

    if isinstance(node, ast.Compare) and op_len == 2:
      if len(node.ops) != 1:
        raise ValueError("Unsupported comparison kind: {} operators".format(len(node.ops)))

      comp = node.ops[0]
      if isinstance(comp, ast.Gt):
        return ops[0] > ops[1]
      if isinstance(comp, ast.Lt):
        return ops[0] < ops[1]
      if isinstance(comp, ast.GtE):
        return ops[0] >= ops[1]
      if isinstance(comp, ast.LtE):
        return ops[0] <= ops[1]
      if isinstance(comp, ast.Eq):
        return ops[0] == ops[1]
      if isinstance(comp, ast.NotEq):
        return ops[0] != ops[1]
      raise ValueError("Unsupported comparator: {} with {} operands".format(type(comp).__name__, op_len))
    
    raise ValueError("Unsupported node type: {} with {} operands".format(type(node).__name__, op_len))
  
  def parse(self, str):
    parsed = ast.parse(str)
    if not isinstance(parsed, ast.Module) or len(parsed.body) != 1:
      raise ValueError("Unrecognized input format")

    expr = parsed.body[0]
    if not isinstance(expr, ast.Expr):
      raise ValueError("Expected an arithmetic expression")

    self.divisors = []
    result_expr = self.visit_node(expr.value)
    for d in self.divisors:
      result_expr = z3.And(result_expr, d != z3.IntVal(0))
    return result_expr
  
  def fix_token(self, token):
    if token == "&&":
      return " and "
    if token == "||":
      return " or "
    if token == "=":
      return "=="
    return token.lower()
  
  def prepare(self, str):
    tokens = re.findall(r'\s+|-\w*|\w+|\(|\)|[^\w\(\)\s-]+', str)
    return "".join([self.fix_token(x) for x in tokens])

class SMTSolver:
  variables = {}

  bot = MathBot()

  def reset(self, variables = ["x", "y", "z"], var_type = "integer"):
    self.solver = z3.Solver()
    self.solver.set(unsat_core=True)
    self.var_type = var_type
    for v in variables:
      if self.var_type == "real":
        self.variables[v] = z3.Real(v)
      else:
        self.variables[v] = z3.Int(v)
    self.cur_assert_id = 0
    self.visitor = ASTVisitor(self.variables, self.var_type)
    self.assertions = {}
    self.cur_constraints = None
  
  def is_tautology(self, new_expr):
    s = z3.Solver()
    s.add(z3.Not(new_expr))
    if self.cur_constraints is not None:
      s.add(self.cur_constraints)

    return s.check() != z3.sat
  
  def is_unique_solution(self, model):
    s = z3.Solver()
    s.add(self.cur_constraints)

    expr = None
    for v in self.variables:
      cur_expr = self.variables[v] != model[self.variables[v]]
      if expr is None:
        expr = cur_expr
      else:
        expr = z3.Or(expr, cur_expr)
    
    if expr is None:
      return True
    
    s.add(expr)
    return s.check() == z3.unsat

  def turn(self, inp):
    expr = None
    inp = self.visitor.prepare(inp)
    try:
      expr = self.visitor.parse(inp)
    except ValueError as e:
      return TurnInfo(TurnResult.MISTAKE, "", str(e)), inp
    except SyntaxError as e:
      return TurnInfo(TurnResult.MISTAKE, "", str(e)), inp
    
    assert_name = "a" + str(self.cur_assert_id)
    debug_expr = str(expr)
    self.assertions[assert_name] = expr

    try:
      if self.is_tautology(expr):
        return TurnInfo(TurnResult.TAUTOLOGY, debug_expr), expr
    except z3.Z3Exception as e:
      return TurnInfo(TurnResult.MISTAKE, debug_expr, str(e)), expr

    try:
      self.solver.assert_and_track(expr, assert_name)
      self.cur_assert_id += 1
    except z3.Z3Exception as e:
      return TurnInfo(TurnResult.MISTAKE, debug_expr, str(e))
    
    if self.cur_constraints is None:
      self.cur_constraints = expr
    else:
      self.cur_constraints = z3.And(self.cur_constraints, expr)

    check_result = self.solver.check()
    if check_result == z3.unsat:
      return TurnInfo(TurnResult.LOST, debug_expr, " and ".join(["(" + str(self.assertions[str(x)]) + ")" for x in self.solver.unsat_core()])), expr

    if check_result == z3.unknown:
      return TurnInfo(TurnResult.DRAW, debug_expr, "The solver is unable to solve the system"), expr
    
    if self.is_unique_solution(self.solver.model()):
      return TurnInfo(TurnResult.DRAW, debug_expr, "The system now has only one solution"), expr

    return TurnInfo(TurnResult.SUCCESS, debug_expr), expr
  
  def get_bot_turn(self):
    variables = list(self.variables.keys())

    max_tries = 10
    for i in range(max_tries):
      inp = self.bot.get_turn(variables)

      solver = SMTSolver()
      solver.reset(variables, self.var_type)

      try:
        expr = self.visitor.parse(self.visitor.prepare(inp))
        solver.solver.assert_exprs(expr)
        if solver.solver.check() != z3.unsat:
          break
      except ValueError as e:
        return f"{variables[0]} == {variables[0]} + 1"
      except SyntaxError as e:
        return f"{variables[0]} == {variables[0]} + 1"
      except z3.Z3Exception as e:
        return f"{variables[0]} == {variables[0]} + 1"

    return inp

  def get_variables():
    return ", ".join(self.variables.keys())
