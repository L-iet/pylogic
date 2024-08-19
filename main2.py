from pylogic.proposition.proposition import Proposition
from pylogic.proposition.quantified.forall import Forall
from pylogic.proposition.quantified.exists import Exists, ExistsInSet
from pylogic.proposition.relation.equals import Equals
from pylogic.variable import Variable
from pylogic.constant import Constant
from pylogic.structures.set_ import Set, Naturals0, Reals

x = Variable("x")
y = Variable("y")
z = Variable("z")


Px = Proposition("P", args=[x])
Py = Proposition("P", args=[y])
p1 = Exists(x, Px)
p2 = ExistsInSet(x, Naturals0, Px)
p3 = Exists(x, x.is_in(Naturals0).and_(Px))

print(p3)
p4 = p3.to_exists_in_set()
print(p4)

p5 = Exists(x, Px.and_(Forall(y, Py.implies(Equals(y, x)))))
print(p5)
p6 = p5.to_exists_unique()
print(p6)

p7 = Exists(
    x, x.is_in(Reals).and_(Px, Forall(y, y.is_in(Reals).and_(Py).implies(Equals(y, x))))
)
print(p7)
p8 = p7.to_exists_unique_in_set()
print(p8)
