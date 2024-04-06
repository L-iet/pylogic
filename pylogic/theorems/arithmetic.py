from pylogic.proposition.quantified.forall import Forall
from pylogic.proposition.relation.equals import Equals
from pylogic.variable import Variable
from sympy import Add, Integer


x = Variable("x", real=True)
y = Variable("y", real=True)
# every number has an additive inverse
x_plus_neg_x = Add(x, -x, evaluate=False)

add_inv = (
    Equals(x_plus_neg_x, Integer(0))
    .by_simplification()
    .thus_there_exists("y", -x)
    .thus_forall(x)
)
