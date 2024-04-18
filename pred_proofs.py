from pylogic.proposition.proposition import Proposition
from pylogic.proposition.implies import Implies
from pylogic.proposition.quantified.forall import Forall
from pylogic.proposition.quantified.exists import Exists
from pylogic.proposition.not_ import neg
from pylogic.proposition.or_ import Or
from pylogic.variable import Variable
from pylogic.proposition.proof_search import proof_search

x = Variable("x")
Px = Proposition("P", args=[x])
Qx = Proposition("Q", args=[x])
Rx = Proposition("R", args=[x])
prem1 = Forall(x, Px, True)
prem2 = Exists(x, Implies(Px, Qx), True)
prem3 = Forall(x, Qx.implies(Rx), True)
exqx = Exists(x, Qx)
exrx = Exists(x, Rx)

P = Proposition("P", True)
Q = Proposition("Q")
R = Proposition("R")
S = Proposition("S")
T = Proposition("T")
PImpQ = Implies(P, Q, True)
QImpR = Implies(Q, R, True)
RImpS = Implies(R, S, True)
SImpT = Implies(S, T)
# prem3 = Implies(QImpR, SImpT, True)

PImpR = Implies(P, R)
PImpT = Implies(P, T)


inf_res = proof_search(
    [
        P,
        QImpR,
        prem1,
        prem2,
        prem3,
        PImpQ,
        Or(S, R, is_assumption=True),
        neg(R, is_assumption=True),
    ],
    S,
)
print(inf_res)
