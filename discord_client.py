#!/usr/bin/env python3

import sys
import discord
from discord import app_commands
from solver import SMTSolver, TurnInfo, TurnResult
from typing import Optional

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

duels = {}

class Duel:
  variables = ["x", "y", "z"]

  def __init__(self, users, var_type = "integer"):
    self.solver = SMTSolver()
    self.var_type = var_type
    if self.var_type != "integer" and self.var_type != "real":
      self.var_type = "integer"
    self.users = users
    self.turn = 0
  
  async def register(self, ctx):
    self.solver.reset(self.variables, self.var_type)
    await ctx.response.send_message(f"{self.users[0].name} вызывает на дуэль {self.users[1].name}!\nСписок переменных: {', '.join(self.variables)}\nТип переменных: {self.var_type}\nИспользуйте команду /math")
    message = await ctx.original_response()
    self.thread = await message.create_thread(name=f"Дуэль {self.users[0].name} и {self.users[1].name}", auto_archive_duration=60)
    duels[self.thread.id] = self
    await self.thread.send(f"Сейчас ход {self.users[self.turn].mention}!", silent=True)
  
  async def make_bot_turn(self):
    expr = get_bot_turn()
    res, fixed_expr = duel.solver.turn(expr)

    input = expr if expr == f"Я делаю свой ход:\n```{expr}```" else f"```{expr}```||```{fixed_expr}```||"
    
    if res.result == TurnResult.SUCCESS:
      duel.turn = (duel.turn + 1) % len(duel.users)
      await self.thread.send(f"{input}\nСейчас ход {duel.users[duel.turn].mention}!", silent=True)
      return
    
    if res.result == TurnResult.MISTAKE:
      await self.thread.send(f"{input}В моём утверждении ошибка: {res.info}", silent=True)
      return
    
    if res.result == TurnResult.TAUTOLOGY:
      await self.thread.send(f"{input}Моё утверждение не вносит ничего нового", silent=True)
      self.make_bot_turn()
      return
    
    if res.result == TurnResult.LOST:
      await self.thread.send(f"{input}Я проиграл. Несовместимый набор утверждений: {res.info}", silent=True)
      duels.pop(self.thread.id, None)
      return
    
    if res.result == TurnResult.DRAW:
      await self.thread.send(f"{input}Ничья. {res.info}", silent=True)
      duels.pop(self.thread.id, None)
      return
    
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
  clear_hall = False

  if clear_hall:
    threads = hall.threads
    for t in threads:
      await t.delete()
    
  mgs = []
  async for x in hall.history(limit=200):
    mgs.append(x)
    
  if clear_hall:
    await hall.delete_messages(mgs)
    mgs = []

  if len(mgs) == 0:
    await hall.send("В клубе наступает новый день!\nМожет, начнём его с хорошей математической дуэли?\nИспользуйте команду /duel <оппонент> <Int/real> начать дуэль!")

@client.event
async def setup_hook():
  await tree.sync()

@tree.command(name = "duel", description = "Вызвать на дуэль")
async def duel(ctx: discord.Interaction, opponent: discord.Member, vartype: Optional[str] = "integer"):
  if ctx.channel.id != hall.id or opponent is None:
    await ctx.response.send_message(f"Дуэли можно объявлять только в канале '{hall.name}'", silent=True)
    return

  duel = Duel([ctx.user, opponent], vartype.strip().lower())
  await duel.register(ctx)

@tree.command(name = "math", description = "Сделать математическое утверждение")
async def math(ctx: discord.Interaction, *, expr: str):
  if ctx.channel.id not in duels:
    await ctx.response.send_message(f"Чтобы начать дуэль, используйте команду /duel с ником оппонента в канале '{hall.name}'", silent=True)
    return

  duel = duels[ctx.channel.id]

  if duel.users[duel.turn].id != ctx.user.id:
    await ctx.response.send_message(f"Сейчас ход {duel.users[duel.turn].name}!", silent=True)
    return

  res, fixed_expr = duel.solver.turn(expr)

  input = expr if expr == f"```{expr}```" else f"```{expr}```||```{fixed_expr}```||"
  
  if res.result == TurnResult.SUCCESS:
    duel.turn = (duel.turn + 1) % len(duel.users)
    await ctx.response.send_message(f"{input}Новое утверждение от {ctx.user.name}.\nСейчас ход {duel.users[duel.turn].mention}!", silent=True)
    if duel.users[duel.turn].id == client.user.id:
      await make_bot_turn(ctx, duel)
    return
  
  if res.result == TurnResult.MISTAKE:
    await ctx.response.send_message(f"{input}В твоём утверждении ошибка: {res.info}", silent=True)
    return
  
  if res.result == TurnResult.TAUTOLOGY:
    await ctx.response.send_message(f"{input}Твоё утверждение не вносит ничего нового", silent=True)
    return
  
  if res.result == TurnResult.LOST:
    await ctx.response.send_message(f"{input}Ты проиграл. Несовместимый набор утверждений: {res.info}", silent=True)
    duels.pop(ctx.channel.id, None)
    return
  
  if res.result == TurnResult.DRAW:
    await ctx.response.send_message(f"{input}Ничья. {res.info}", silent=True)
    duels.pop(ctx.channel.id, None)
    return

client.run(sys.argv[1])