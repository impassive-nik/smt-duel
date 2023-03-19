#!/usr/bin/env python3

from solver import SMTSolver, TurnInfo, TurnResult

variables = ["x", "y", "z"]

solver = SMTSolver()
solver.reset(variables)

while True:
  inp = input()
  res, fixed_expr = solver.turn(inp)
  
  if res.result == TurnResult.SUCCESS:
    print("Success")
    continue
  
  if res.result == TurnResult.MISTAKE:
    print("Mistake: {}".format(res.info))
    continue
  
  if res.result == TurnResult.TAUTOLOGY:
    print("The statement gives no new information")
    continue
  
  if res.result == TurnResult.LOST:
    print("You lost. Unsatisfiable constraints: {}".format(res.info))
    break
  
  if res.result == TurnResult.DRAW:
    print("Draw. {}".format(res.info))
    break  
  