from pylogic.proposition.proposition import Proposition
from pylogic.proposition.implies import Implies
from pylogic.proposition.quantified.forall import Forall
from pylogic.proposition.quantified.exists import Exists
from pylogic.variable import Variable

x = Variable("x")
Px = Proposition("P", args=[x])
Qx = Proposition("Q", args=[x])
prem1 = Forall(x, Px, True)
prem2 = Exists(x, Implies(Px, Qx), True)
print(prem1.quantified_modus_ponens(prem2).is_proven)
