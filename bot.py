import random

class MathBot:
  def __init__(self, max_depth = 2):
    self.max_depth = max_depth
    self.variables = []

  def gen_var(self, depth):
    if depth >= self.max_depth or random.randint(0, 2) == 0:
      return random.choice(self.variables)
    operations = ["+", "-", "*", "/"]
    return f"({self.gen_var(depth + 1)} {random.choice(operations)} {self.gen_value(depth + 1)})"

  def gen_value(self, depth):
    if depth >= self.max_depth or random.randint(0, 2) == 0:
      if random.randint(0, 10) <= 7:
        return random.choice(["-", "", "", ""]) + str(random.randint(1, 25) * pow(10, random.randint(0, 3)) + random.randint(1, 9))
      else:
        return random.choice(["-", "", "", ""]) + random.choice(self.variables)
    operations = ["+", "-", "*", "/"]
    return f"({self.gen_var(depth + 1)} {random.choice(operations)} {self.gen_value(depth + 1)})"

  def gen_bool(self, depth):
    if self.max_depth == depth or random.randint(0, 8) <= 6:
      operations = ["<=", "<", "==", "!=", ">", ">="]
      return f"{self.gen_var(depth + 1)} {random.choice(operations)} {self.gen_value(depth + 1)}"

    operations = ["and", "or"]
    return f"{self.gen_bool(depth + 1)} {random.choice(operations)} {self.gen_bool(depth + 1)}"

  def get_turn(self, variables):
    self.variables = variables
    return self.gen_bool(0)
