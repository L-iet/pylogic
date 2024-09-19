from pylogic.constant import Constant
from pylogic.proposition.proposition import Proposition
from pylogic.proposition.quantified.exists import Exists, ExistsInSet
from pylogic.proposition.quantified.forall import Forall
from pylogic.proposition.relation.equals import Equals
from pylogic.structures.set_ import Set
from pylogic.variable import Variable


def log(*args, **kwargs):
    if printing:
        print(*args, **kwargs)


printing = False
x = Variable("x")
y = Variable("y")
z = Variable("z")

Naturals0 = Set("Naturals0", elements={0, 1, 2, 3, 4, 5, 6, 7, 8, 9})
Reals = Set("Reals")

Px = Proposition("P", args=[x])
Py = Proposition("P", args=[y])
p1 = Exists(x, Px)
p2 = ExistsInSet(x, Naturals0, Px)
p3 = Exists(x, x.is_in(Naturals0).and_(Px))

log(p3)
p4 = p3.to_exists_in_set()
log(p4)

p5 = Exists(x, Px.and_(Forall(y, Py.implies(Equals(y, x)))))
log(p5)
p6 = p5.to_exists_unique()
log(p6)

p7 = Exists(
    x, x.is_in(Reals).and_(Px, Forall(y, y.is_in(Reals).and_(Py).implies(Equals(y, x))))
)
log(p7)
p8 = p7.to_exists_unique_in_set()
log(p8)

x = Variable("x", real=True)
log(b := x.to_sympy()._pyl_init_kwargs, type(b))


printing = True
a, b, c, x, y, z = [Variable(i) for i in "abcxyz"]


def P(*args):
    return Proposition("P", args=list(args))  # type: ignore


p1 = Forall(a, Exists(x, P(x, a)), is_assumption=True)
p2 = p1.in_particular(a)
p3_var, p3 = p2.extract()
# p4 = p3.thus_forall(a)
# p5 = p4.thus_there_exists("x", p3_var) # error since p3_var depends on a, and a is bound from p4
p6 = p3.thus_there_exists("x", p3_var)
log(p6)
