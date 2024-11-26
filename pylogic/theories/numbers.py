from pylogic.expressions.gcd import Gcd
from pylogic.helpers import Namespace
from pylogic.inference import Inference
from pylogic.proposition.quantified.exists import ExistsInSet
from pylogic.proposition.quantified.forall import ForallInSet
from pylogic.theories.integers import Integers
from pylogic.theories.natural_numbers import Naturals
from pylogic.theories.rational_numbers import Rationals
from pylogic.theories.real_numbers import Reals
from pylogic.variable import Variable

N_subset_Z = Naturals.is_subset_of(Integers, is_axiom=True)
N_subset_Q = Naturals.is_subset_of(Rationals).todo(_internal=True)
N_subset_R = Naturals.is_subset_of(Reals).todo(_internal=True)
Z_subset_Q = Integers.is_subset_of(Rationals, is_axiom=True)
Z_subset_R = Integers.is_subset_of(Reals).todo(_internal=True)
Q_Subset_R = Rationals.is_subset_of(Reals, is_axiom=True)
Naturals.subset_relations = Namespace(
    N_subset_Z=N_subset_Z,
    N_subset_Q=N_subset_Q,
    N_subset_R=N_subset_R,
)
Integers.subset_relations = Namespace(
    N_subset_Z=N_subset_Z,
    Z_subset_Q=Z_subset_Q,
    Z_subset_R=Z_subset_R,
)
Rationals.subset_relations = Namespace(
    N_subset_Q=N_subset_Q,
    Z_subset_Q=Z_subset_Q,
    Q_Subset_R=Q_Subset_R,
)
Reals.subset_relations = Namespace(
    N_subset_R=N_subset_R,
    Z_subset_R=Z_subset_R,
    Q_Subset_R=Q_Subset_R,
)

r, p, q, a, b, c, k = map(Variable, "r p q a b c k".split())

Rationals.theorems = Namespace()
Integers.theorems = Namespace()

Rationals.theorems.ratio_of_integers_lowest_terms = ForallInSet(
    r,
    Rationals,
    ExistsInSet(
        p, Integers, ExistsInSet(q, Integers, r.equals(p / q).and_(Gcd(p, q).equals(1)))
    ),
).todo(_internal=True)

prime_divides_product = ForallInSet(
    p,
    Naturals,
    ForallInSet(
        a,
        Integers,
        ForallInSet(
            b,
            Integers,
            Naturals.prime(p)
            .and_(Integers.divides(p, a * b))
            .implies(Integers.divides(p, a).or_(Integers.divides(p, b))),
        ),
    ),
).todo(_internal=True)

prime_divides_power = ForallInSet(
    p,
    Naturals,
    ForallInSet(
        a,
        Integers,
        ForallInSet(
            k,
            Naturals,
            Naturals.prime(p)
            .and_(Integers.divides(p, a**k))
            .implies(Integers.divides(p, a)),
        ),
    ),
).todo(_internal=True)
Integers.theorems.division_theorems = Namespace(
    {
        "prime": {
            "prime_divides_product": prime_divides_product,
            "prime_divides_power": prime_divides_power,
        },
        "product": ForallInSet(
            a,
            Integers,
            ForallInSet(
                b,
                Integers,
                ForallInSet(
                    c,
                    Integers,
                    a.equals(b * c).implies(
                        Integers.divides(b, a).and_(Integers.divides(c, a))
                    ),
                ),
            ),
        ).todo(_internal=True),
        "gcd": ForallInSet(
            a,
            Integers,
            ForallInSet(
                b,
                Integers,
                ForallInSet(
                    c,
                    Integers,
                    Integers.divides(a, b)
                    .and_(Integers.divides(a, c))
                    .implies(Integers.divides(a, Gcd(b, c))),
                ),
            ),
        ).todo(_internal=True),
    }
)
