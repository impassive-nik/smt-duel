#!/usr/bin/env python3

from solver import SMTSolver, TurnInfo, TurnResult

variables = ["x", "y", "z"]

solver = SMTSolver()
solver.reset()

while True:
  inp = input()
  res = solver.turn(inp)
  print(res.debug)
  
  if res.result == TurnResult.SUCCESS:
    print("Success")
    continue
  
  if res.result == TurnResult.MISTAKE:
    print("Mistake: {}".format(res.info))
    continue
  
  if res.result == TurnResult.LOST:
    print("You lost. {}".format(res.info))
    break
  
  if res.result == TurnResult.DRAW:
    print("Draw. {}".format(res.info))
    break  
  