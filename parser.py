import re
from collections import deque

unary_ops = ["not"]
binary_ops = ["+", "-", "*", "/", "=", "<=", ">=", "<", ">", "or", "and"]
translation_map = {"==" : "=", "!" : "not", "||" : "or", "&&" : "and"}

def translate(x):
  if x in translation_map:
    return translation_map[x]
  return x

def get_priority(x):
  if x in unary_ops:
    return 4
  if x in ["<=", "<", ">", ">=", "="]:
    return 1
  if x in ["+", "-"]:
    return 2
  if x in ["*", "/"]:
    return 3
  if x in ["(", ")"]:
    return -1
  return 0

def is_operand(x):
  return x in binary_ops or x in unary_ops

def is_unary(x):
  return x in unary_ops

def ignored(x):
  return x in ["(", ")"]

def prefix_notation(A, variables):
  stack = deque()
  A = '(' + A.strip() + ')'
  output = []
  words = [translate(x.strip()) for x in re.findall(r'-\d*|\w+|\(|\)|[^\w\(\)\s-]+|\s+', A)][::-1]
  for c in words:
    if c == "":
      continue
    if c == ")":
      stack.append(c)
    elif is_operand(c):
      while get_priority(c) < get_priority(stack[-1]):
        output.append(stack.pop())
      stack.append(c)
    elif c == "(":
      while stack:
        c1 = stack.pop()
        if c1 == ')':
          break
        output.append(c1)
    elif c in variables:
      output.append(c)
    elif c.isnumeric() or (c.startswith("-") and c[1:].isnumeric()):
      output.append(c)
    else:
      if c.isalnum():
        raise ValueError("Unknown variable: {}, expected {}".format(c, ", ".join(variables)))
      else:
        raise ValueError("Unknown operation: {}, expected {}".format(c, ", ".join(unary_ops + binary_ops)))

  while stack:
    op = stack.pop()
    if not ignored(op):
      output.append(op)
    
  result = []
  counter = 0
  for op in output[::-1]:
    result.append(op)
    counter -= 1
    if is_operand(op):
      result[-1] = "(" + result[-1]
      stack.append(counter)
      counter = 1 if is_unary(op) else 2
    else:
      while counter == 0:
        result[-1] += ")"
        if not stack:
          break
        counter = stack.pop()

  return " ".join(result)