from pylogic.assumptions_context import AssumptionsContext, conclude
from pylogic.proposition.proposition import Proposition
from pylogic.proposition.quantified.forall import Forall, ForallInSet
from pylogic.proposition.relation.contains import IsContainedIn
from pylogic.structures.set_ import Set
from pylogic.variable import Variable

x1 = Variable("x1")
a1 = Forall(x1, Proposition("P", args=[x1]), is_assumption=True)

x2 = Variable("x2")
a2 = Forall(
    x2,
    Proposition("P", args=[x2]).implies(Proposition("Q", args=[x2])),
    is_assumption=True,
)

ctx = AssumptionsContext().open()
x3 = Variable("x3")

px3 = a1(x3)
px3_implies_qx3 = a2(x3)
qx3 = px3.modus_ponens(px3_implies_qx3)
conclude(qx3)
print(ctx.get_proven())

ctx.close()
print(ctx.get_proven())

x4 = Variable("x4")
S = Set("S")
Px4 = Proposition("P", args=[x4])
Qx4 = Proposition("Q", args=[x4])
a1 = ForallInSet(x4, S, Px4.implies(Qx4), is_assumption=True)
x5 = Variable("x5")
Qx5 = Proposition("Q", args=[x5])
Rx5 = Proposition("R", args=[x5])
a2 = Forall(x5, Qx5.implies(Rx5), is_assumption=True)


with AssumptionsContext() as ctx:
    x6 = Variable("x6")
    x6_in_S = IsContainedIn(x6, S).assume()
    with AssumptionsContext() as ctx2:
        Px6 = Proposition("P", args=[x6]).assume()
        Qx6 = Px6.modus_ponens(a1(x6))
        Rx6 = Qx6.modus_ponens(a2(x6))
        conclude(Rx6)
    Px6_imp_Rx6 = ctx2.get_proven()[0]
    conclude(Px6_imp_Rx6)
print(ctx.get_proven())
