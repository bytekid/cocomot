
def spaces(n):
  return "" if n <= 0 else " " + spaces(n-1) 


def pad_to(s, n):
  return s + spaces(n - len(s)) if len(s) < n else s[:n]

