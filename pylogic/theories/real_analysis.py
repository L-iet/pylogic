from pylogic.proposition.quantified.forall import Forall, ForallInSet
from pylogic.proposition.quantified.exists import Exists, ExistsInSet
from pylogic.proposition.relation.equals import Equals
from pylogic.proposition.or_ import Or
from pylogic.proposition.exor import ExOr
from pylogic.proposition.and_ import And
from pylogic.proposition.not_ import Not, neg
from pylogic.variable import Variable, variables
from pylogic.constant import Constant
from pylogic.structures.sets import Set, Reals

from pylogic.expressions.expr import add, mul, sub
from pylogic.infix.is_ import is_, equals
from pylogic.infix.by import by
from pylogic.helpers import assume

import sympy as sp

a, b, c, d, f, h, t = variables("a", "b", "c", "d", "f", "h", "t", real=True)
x = Variable("x", real=True)
zero = Constant(0, real=True)
one = Constant(1, real=True)

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
                add(add(a, b), c),
                add(a, add(b, c)),
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
            add(a, b),
            add(b, a),
        ),
    ),
    description="Addition is commutative",
    is_axiom=True,
)


def is_additive_identity(z, is_axiom=False, is_assumption=False):
    return ForallInSet(
        a,
        Reals,
        Equals(add(a, z), a),
        description=f"{z} is an additive identity of real numbers",
        is_axiom=is_axiom,
        is_assumption=is_assumption,
    )


zero_exists = is_additive_identity(zero, is_axiom=True)

add_inv = ForallInSet(
    a,
    Reals,
    ExistsInSet(
        b,
        Reals,
        Equals(add(a, b), zero),
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
                mul(mul(a, b), c),
                mul(a, mul(b, c)),
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
            mul(a, b),
            mul(b, a),
        ),
    ),
    description="Multiplication is commutative",
    is_axiom=True,
)

one_neq_zero = neg(Equals(one, zero), description="1 is not equal to 0", is_axiom=True)


def is_multiplicative_identity(t, is_axiom=False, is_assumption=False):
    return ForallInSet(
        a,
        Reals,
        Equals(mul(a, t), a),
        description=f"{t} is a multiplicative identity of real numbers",
        is_axiom=is_axiom,
        is_assumption=is_assumption,
    )


one_exists = is_multiplicative_identity(one, is_axiom=True)


mul_inv = ForallInSet(
    a,
    Reals,
    neg(Equals(a, zero)).implies(
        ExistsInSet(
            b,
            Reals,
            Equals(
                mul(a, b),
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
                mul(a, add(b, c)),
                add(mul(a, b), mul(a, c)),
            ),
        ),
    ),
    description="Multiplication distributes over addition",
    is_axiom=True,
)

# Theorems
# 0 is unique
d_eq_d_plus_0 = zero_exists.in_particular(d).symmetric()
d_plus_0_eq_0_plus_d = add_comm.in_particular(d).in_particular(zero)
forall_a_in_reals_a_plus_d_eq_a = is_additive_identity(d, is_assumption=True)
zero_plus_d_eq_0 = forall_a_in_reals_a_plus_d_eq_a.in_particular(zero)
d_eq_0 = d_eq_d_plus_0.transitive(d_plus_0_eq_0_plus_d).transitive(zero_plus_d_eq_0)
zero_unique = zero_exists.p_and(
    d_eq_0.followed_from(forall_a_in_reals_a_plus_d_eq_a).thus_forall(d)
).set_description("The additive identity of real numbers is unique")

# another style of proof, same proof
additive_identity = is_additive_identity
p1 = d + 0 | equals | d | by | zero_exists
p2 = d | equals | d + 0 | by(p1, rule="symmetric")
p3 = d + 0 | equals | 0 + d | by | add_comm
forall_a_in_reals_a_plus_d_eq_a = assume(d | is_ | additive_identity)
p4 = 0 + d | equals | 0 | by | forall_a_in_reals_a_plus_d_eq_a  # type: ignore
p5 = d | equals | 0 + d | by(p2, p3, rule="transitive")
p6 = d | equals | 0 | by(p5, p4, rule="transitive")
zero_unique2 = zero_exists.p_and(p6.close_all_scopes())

# 1 is unique
d_eq_d_times_1 = one_exists.in_particular(d).symmetric()
d_times_1_eq_1_times_d = mul_comm.in_particular(d).in_particular(one)
forall_a_in_reals_a_times_d_eq_a = is_multiplicative_identity(d, is_assumption=True)
one_times_d_eq_1 = forall_a_in_reals_a_times_d_eq_a.in_particular(one)
d_eq_1 = d_eq_d_times_1.transitive(d_times_1_eq_1_times_d).transitive(one_times_d_eq_1)
forall_d_eq_1 = d_eq_1.close_all_scopes()
one_unique = one_exists.p_and(forall_d_eq_1).set_description(
    "The multiplicative identity of real numbers is unique"
)
