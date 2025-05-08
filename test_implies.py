from pylogic import *

p = proposition("p")

q = contradiction.implies(p, dont_prove=True)
r = contradiction.implies(p)
s = contradiction.implies(p, is_assumption=True)
print(q.is_proven)
print(q.deduced_from)

print(r.is_proven)
print(r.deduced_from)

print(s.is_proven)
print(s.deduced_from)

print(p.implies(p).is_proven)
print(p.implies(p).deduced_from)
