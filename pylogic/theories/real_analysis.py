from pylogic.proposition.quantified.forall import Forall, ForallInSet
from pylogic.proposition.quantified.exists import Exists, ExistsInSet
from pylogic.proposition.relation.equals import Equals
from pylogic.proposition.or_ import Or
from pylogic.proposition.exor import ExOr
from pylogic.proposition.and_ import And
from pylogic.proposition.not_ import Not, neg
from pylogic.variable import Variable
from pylogic.constant import Constant
from pylogic.structures.sets import Set, Reals

import sympy as sp

a, b, c = Variable("a", real=True), Variable("b", real=True), Variable("c", real=True)
zero = Variable("0", real=True)
one = Variable("1", real=True)
add_assoc = ForallInSet(
    a,
    Reals,
    ForallInSet(
        b,
        Reals,
        ForallInSet(
            c,
            Reals,
            Equals(
                sp.Add(sp.Add(a, b, evaluate=False), c, evaluate=False),
                sp.Add(a, b + c, evaluate=False),
            ),
        ),
    ),
    description="Addition is associative",
    is_axiom=True,
)

add_comm = ForallInSet(
    a,
    Reals,
    ForallInSet(
        b,
        Reals,
        Equals(sp.Add(a, b, evaluate=False), sp.Add(b, a, evaluate=False)),
    ),
    description="Addition is commutative",
    is_axiom=True,
)
