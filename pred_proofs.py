from pylogic.proposition.proposition import Proposition
from pylogic.proposition.implies import Implies
from pylogic.proposition.quantified.forall import Forall
from pylogic.proposition.quantified.exists import Exists
from pylogic.proposition.not_ import neg
from pylogic.proposition.or_ import Or
from pylogic.proposition.and_ import And
from pylogic.variable import Variable
from pylogic.proposition.proof_search import proof_search

x = Variable("x")
Px = Proposition("P", args=[x])
Qx = Proposition("Q", args=[x])
Rx = Proposition("R", args=[x])
prem1 = Forall(x, Px, True)
prem2 = Forall(x, Implies(Px, Qx), True)
prem3 = Forall(x, Qx.implies(Rx), True)
exqx = Exists(x, Qx)
exrx = Exists(x, Rx)

P = Proposition("P", True)
Q = Proposition("Q", True)
R = Proposition("R", True)
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
        Q,
        R,
        prem1,
        prem2,
        prem3,
        And(P, Q, R).implies(S, True),
        # Or(S, R, is_assumption=True),
    ],
    Proposition("R", args=[5]),
)
print(inf_res)
