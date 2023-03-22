#!/usr/bin/env python3

from solver import SMTSolver, TurnInfo, TurnResult

variables = ["x", "y", "z"]

solver = SMTSolver()
solver.reset(variables, "int")

class Player:
  def __init__(self, name):
    self.name = name
  
  def get_input(self):
    return input()

class Bot:
  def __init__(self, name):
    self.name = name
  
  def get_input(self):
    turn = solver.get_bot_turn()
    print(turn)
    return turn

players = [Player("Human"), Bot("Bot")]
cur_player = 0

while True:
  print(f"{players[cur_player].name}, it's your turn!")
  res, fixed_expr = solver.turn(players[cur_player].get_input())
  
  if res.result == TurnResult.SUCCESS:
    print("Accepted")
    cur_player = (cur_player + 1) % len(players)
    continue
  
  if res.result == TurnResult.MISTAKE:
    print(f"Mistake: {res.info}")
    continue
  
  if res.result == TurnResult.TAUTOLOGY:
    print("The statement gives no new information")
    continue
  
  if res.result == TurnResult.LOST:
    print(f"{players[cur_player].name} lost. Unsatisfiable constraints: {res.info}")
    break
  
  if res.result == TurnResult.DRAW:
    print(f"Draw. {res.info}")
    break
  