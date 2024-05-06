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
x = Variable("x", real=True)
zero = Constant("0", real=True)
one = Constant("1", real=True)

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
                (sp.Add(sp.Add(a, b, evaluate=False), c, evaluate=False)),
                (sp.Add(a, b + c, evaluate=False)),
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
        Equals(
            (sp.Add(a, b, evaluate=False)),
            (sp.Add(b, a, evaluate=False)),
        ),
    ),
    description="Addition is commutative",
    is_axiom=True,
)


def is_additive_identity(z, is_axiom=False, is_assumption=False):
    return ForallInSet(
        a,
        Reals,
        Equals((sp.Add(a, z, evaluate=False)), a),
        description=f"{z} is an additive identity of real numbers",
        is_axiom=is_axiom,
        is_assumption=is_assumption,
    )


zero_exists = is_additive_identity(zero, True)

add_inv = ForallInSet(
    a,
    Reals,
    ExistsInSet(
        b,
        Reals,
        Equals((sp.Add(a, b, evaluate=False)), zero),
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
                (sp.Mul(sp.Mul(a, b, evaluate=False), c, evaluate=False)),
                (sp.Mul(a, b * c, evaluate=False)),
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
        Equals(
            (sp.Mul(a, b, evaluate=False)),
            (sp.Mul(b, a, evaluate=False)),
        ),
    ),
    description="Multiplication is commutative",
    is_axiom=True,
)

one_exists = neg(Equals(one, zero)).and_(
    ForallInSet(a, Reals, Equals((sp.Mul(a, one, evaluate=False)), a)),
    description=f"{one} is a multiplicative identity of real numbers",
    is_axiom=True,
)

mul_inv = ForallInSet(
    a,
    Reals,
    neg(Equals(a, zero)).implies(
        ExistsInSet(
            b,
            Reals,
            Equals(
                sp.Mul(a, b, evaluate=False),
                one,
            ),
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
                (sp.Mul(a, sp.Add(b, c, evaluate=False), evaluate=False)),
                (
                    sp.Add(
                        sp.Mul(a, b, evaluate=False),
                        sp.Mul(a, c, evaluate=False),
                        evaluate=False,
                    )
                ),
            ),
        ),
    ),
    description="Multiplication distributes over addition",
    is_axiom=True,
)

# theorems
zero_unique = zero_exists.and_(
    ForallInSet(b, Reals, is_additive_identity(b).implies(Equals(b, zero)))
)
p1 = zero_exists.in_particular(b)
p2 = add_comm.in_particular(zero).in_particular(b)
p3 = is_additive_identity(b, is_assumption=True)
p4 = p3.in_particular(zero)

print(p1, p2, p3, p4, sep="\n")
