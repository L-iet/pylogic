from pylogic.proposition.proposition import Proposition
from pylogic.proposition.implies import Implies
from pylogic.proposition.quantified.forall import Forall
from pylogic.proposition.quantified.exists import Exists
from pylogic.variable import Variable
from pylogic.proposition.proof_search import proof_search

x = Variable("x")
Px = Proposition("P", args=[x])
Qx = Proposition("Q", args=[x])
prem1 = Forall(x, Px, True)
prem2 = Exists(x, Implies(Px, Qx), True)

P = Proposition("P", True)
Q = Proposition("Q")
PImpQ = Implies(P, Q, True)

print(proof_search([P, PImpQ], Q))
