#!/usr/bin/env python3

import sys
import discord
from discord import app_commands
from solver import SMTSolver, TurnInfo, TurnResult

if len(sys.argv) != 2:
  print("Error: expected bot token as the only argument", file=sys.stderr)
  sys.exit(1)

intents = discord.Intents.all()
intents.members = True
intents.reactions = True
intents.guilds = True

client = discord.Client(command_prefix='/', intents=intents)
tree = app_commands.CommandTree(client)

club = None
clubmen = None
hall = None

class Duel:
  variables = ["x", "y", "z"]

  def __init__(self):
    self.solver = SMTSolver()
  
  async def reset(self, channel):
    self.solver.reset(self.variables)
    await channel.send(f"Начинается новый раунд!\nСписок переменных: {', '.join(self.variables)}\nИспользуйте команду /math")

cur_duel = Duel()
    
@client.event
async def on_ready():
  global club
  global clubmen
  global hall

  if len(client.guilds) != 1:
    print(f"I was looking for 'The Club'... found {len(client.guilds)} servers instead")
    exit(1)
  club = client.guilds[0]
  print(f"Entering the {club.name}")

  # Get the clubmen role
  clubmen = discord.utils.get(club.roles, name="Математик")
  if clubmen:
    print(f"Found the role {clubmen.name}")

  # Make everyone "anonymous"
  i = 1
  for member in club.members:
    if member == client.user:
      continue
    #await member.edit(nick = f"Участник {i}")
    i += 1
    if clubmen:
      await member.add_roles(clubmen)

  # Get the club hall
  hall = discord.utils.get(club.text_channels, name="клуб")
  if hall:
    print(f"Found the hall {hall.name}")
  else:
    print(f"Could not find the club hall")
    exit(1)
  
  # Clear the hall
  mgs = [] 
  async for x in hall.history(limit=200):
    mgs.append(x)
  await hall.delete_messages(mgs)
  await cur_duel.reset(hall)

@client.event
async def setup_hook():
  await tree.sync()

@tree.command(name = "math", description = "Сделать математическое утверждение")
async def math(ctx: discord.Interaction, *, expr: str):
  if ctx.channel != hall:
    return

  res, fixed_expr = cur_duel.solver.turn(expr)

  input = expr if expr == f"```{expr}```" else f"```{expr}```||```{fixed_expr}```||"
  
  if res.result == TurnResult.SUCCESS:
    await ctx.response.send_message(f"{input}Новое утверждение от {ctx.user.name}", silent=True)
    return
  
  if res.result == TurnResult.MISTAKE:
    await ctx.response.send_message(f"{input}В твоём утверждении ошибка: {res.info}", silent=True)
    return
  
  if res.result == TurnResult.TAUTOLOGY:
    await ctx.response.send_message(f"{input}Твоё утверждение не вносит ничего нового", silent=True)
    return
  
  if res.result == TurnResult.LOST:
    await ctx.response.send_message(f"{input}Ты проиграл. Несовместимый набор утверждений: {res.info}", silent=True)
    await cur_duel.reset(hall)
    return
  
  if res.result == TurnResult.DRAW:
    await ctx.response.send_message(f"{input}Ничья. {res.info}", silent=True)
    await cur_duel.reset(hall)
    return

client.run(sys.argv[1])