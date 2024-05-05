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

# field axioms
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

zero_exists = ExistsInSet(
    zero,
    Reals,
    ForallInSet(a, Reals, Equals(sp.Add(a, zero, evaluate=False), a)),
    description="Zero (additive identity) exists",
    is_axiom=True,
)

add_inv = ForallInSet(
    a,
    Reals,
    ExistsInSet(
        b,
        Reals,
        Equals(sp.Add(a, b, evaluate=False), zero),
    ),
    description="Every real number has an additive inverse",
    is_axiom=True,
)

mul_assoc = ForallInSet(
    a,
    Reals,
    ForallInSet(
        b,
        Reals,
        ForallInSet(
            c,
            Reals,
            Equals(
                sp.Mul(sp.Mul(a, b, evaluate=False), c, evaluate=False),
                sp.Mul(a, b * c, evaluate=False),
            ),
        ),
    ),
    description="Multiplication is associative",
    is_axiom=True,
)

mul_comm = ForallInSet(
    a,
    Reals,
    ForallInSet(
        b,
        Reals,
        Equals(sp.Mul(a, b, evaluate=False), sp.Mul(b, a, evaluate=False)),
    ),
    description="Multiplication is commutative",
    is_axiom=True,
)

one_exists = ExistsInSet(
    one,
    Reals,
    neg(Equals(one, zero)).and_(
        ForallInSet(a, Reals, Equals(sp.Mul(a, one, evaluate=False), a))
    ),
    description="One (multiplicative identity) exists",
    is_axiom=True,
)

mul_inv = ForallInSet(
    a,
    Reals,
    neg(Equals(a, zero)).implies(
        ExistsInSet(
            b,
            Reals,
            Equals(sp.Mul(a, b, evaluate=False), one),
        )
    ),
    description="Every nonzero real number has a multiplicative inverse",
    is_axiom=True,
)

distributive = ForallInSet(
    a,
    Reals,
    ForallInSet(
        b,
        Reals,
        ForallInSet(
            c,
            Reals,
            Equals(
                sp.Mul(a, sp.Add(b, c, evaluate=False), evaluate=False),
                sp.Add(
                    sp.Mul(a, b, evaluate=False),
                    sp.Mul(a, c, evaluate=False),
                    evaluate=False,
                ),
            ),
        ),
    ),
    description="Multiplication distributes over addition",
    is_axiom=True,
)
