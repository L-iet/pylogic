from pylogic.expressions.expr import cbrt, sqrt
from pylogic.expressions.gcd import Gcd
from pylogic.expressions.prod import Prod
from pylogic.helpers import Namespace
from pylogic.inference import Inference
from pylogic.proposition.not_ import neg
from pylogic.proposition.ordering.greaterorequal import GreaterOrEqual
from pylogic.proposition.ordering.greaterthan import GreaterThan
from pylogic.proposition.ordering.lessorequal import LessOrEqual
from pylogic.proposition.ordering.lessthan import LessThan
from pylogic.proposition.quantified.exists import ExistsInSet
from pylogic.proposition.quantified.forall import ForallInSet
from pylogic.proposition.relation.equals import Equals
from pylogic.structures.set_ import AllFiniteSequences, SeqSet
from pylogic.theories.integers import Integers
from pylogic.theories.natural_numbers import Naturals, one, zero
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

r, p, q, a, b, c, k, w, m, n, i = map(Variable, "r p q a b c k w m n i".split())
k_nat = Variable("k_nat")
k_nat._is_natural = True

a_seq, s_seq = map(
    lambda s: Variable(s, finite=True, sequence=True, length=k_nat),
    "a s".split(),
)
a_seq_set, s_seq_set = map(SeqSet, (a_seq, s_seq))
prod_s_seq = Prod(s_seq)
s_k = s_seq[k]
s_i = s_seq[i]

Reals.theorems.either_rational_or_irrational = ForallInSet(
    r,
    Reals,
    r.is_in(Rationals).xor(neg(r.is_in(Rationals))),
).todo(_internal=True)
Reals.theorems.completeness = Reals.bounded_above_has_lub

Reals.theorems.triangle_inequality = ForallInSet(
    a, Reals, ForallInSet(b, Reals, LessOrEqual(abs(a + b), abs(a) + abs(b)))
).todo(_internal=True)

Rationals.theorems.ratio_of_integers_lowest_terms = ForallInSet(
    r,
    Rationals,
    ExistsInSet(
        p,
        Integers,
        ExistsInSet(
            q,
            Integers,
            neg(q.equals(0)).and_(r.equals(p / q), Gcd(p, q).equals(1)),
        ),
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
prime_irreducible = ForallInSet(
    p,
    Naturals,
    Naturals.prime(p).iff(
        ForallInSet(
            a,
            Naturals,
            ForallInSet(
                b, Naturals, p.equals(a * b).implies(a.equals(1).xor(b.equals(1)))
            ),
        ),
    ),
    description="primes are irreducible",
).todo(_internal=True)
prime_irreducible_b = ForallInSet(
    p,
    Naturals,
    Naturals.prime(p).iff(
        GreaterThan(p, 1).and_(
            ForallInSet(
                a,
                Naturals,
                Naturals.divides(a, p).implies(a.equals(1).or_(a.equals(p))),
            ),
        ),
    ),
).todo(_internal=True)
nat_divides_implies_int_divides = ForallInSet(
    n,
    Naturals,
    ForallInSet(
        m,
        Naturals,
        Naturals.divides(n, m).implies(Integers.divides(n, m)),
    ),
).todo(_internal=True)

prime_gt_1 = ForallInSet(
    p,
    Naturals,
    Naturals.prime(p).implies(GreaterThan(p, 1)),
    description="primes are greater than 1",
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
mul_divisible_by_factors = ForallInSet(
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
).todo(_internal=True)
common_factor_divides_gcd = ForallInSet(
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
).todo(_internal=True)

divides_1_eq_1 = ForallInSet(
    n, Naturals, Naturals.divides(n, 1).implies(Equals(n, 1))
).todo(_internal=True)

divides_1_eq_1_or_minus1 = ForallInSet(
    a, Integers, Integers.divides(a, 1).implies(Equals(a, 1).or_(Equals(a, -1)))
).todo(_internal=True)

prime_sqrt_irrational = ForallInSet(
    n, Naturals, Naturals.prime(n).implies(neg(sqrt(n).is_in(Rationals)))
).todo(_internal=True)
prime_cbrt_irrational = ForallInSet(
    n, Naturals, Naturals.prime(n).implies(neg(cbrt(n).is_in(Rationals)))
).todo(_internal=True)

root_2_irrational = neg(sqrt(2).is_in(Rationals)).todo(_internal=True)
root_3_irrational = neg(sqrt(3).is_in(Rationals)).todo(_internal=True)
cbrt_2_irrational = neg(cbrt(2).is_in(Rationals)).todo(_internal=True)
cbrt_3_irrational = neg(cbrt(3).is_in(Rationals)).todo(_internal=True)

Reals.theorems.root_2_irrational = root_2_irrational
Reals.theorems.root_3_irrational = root_3_irrational
Reals.theorems.cbrt_2_irrational = cbrt_2_irrational
Reals.theorems.cbrt_3_irrational = cbrt_3_irrational
Reals.theorems.prime_sqrt_irrational = prime_sqrt_irrational
Reals.theorems.prime_cbrt_irrational = prime_cbrt_irrational


Integers.theorems.division_theorems = Namespace(
    {
        "prime": {
            "prime_divides_product": prime_divides_product,
            "prime_divides_power": prime_divides_power,
        },
        "mul": mul_divisible_by_factors,
        "gcd": common_factor_divides_gcd,
        "nat_divides_implies_int_divides": nat_divides_implies_int_divides,
        "divides_1_eq_1_or_minus1": divides_1_eq_1_or_minus1,
    }
)

neq_1_has_prime_divisor_int = ForallInSet(
    k,
    Integers,
    neg(Equals(k, 1))
    .and_(neg(Equals(k, -1)))
    .implies(ExistsInSet(p, Naturals, Naturals.prime(p).and_(Integers.divides(p, k)))),
).todo(_internal=True)

Integers.theorems.prime_theorems = Namespace(
    {
        "prime_divides_product": prime_divides_product,
        "prime_divides_power": prime_divides_power,
        "neq_1_has_prime_divisor": neq_1_has_prime_divisor_int,
    }
)

Naturals.theorems.division_theorems = Namespace(
    {
        "prime": {
            "prime_divides_product": prime_divides_product,
            "prime_divides_power": prime_divides_power,
        },
        "mul": mul_divisible_by_factors,
        "nat_divides_implies_int_divides": nat_divides_implies_int_divides,
        "divides_1_eq_1": divides_1_eq_1,
    }
)
mul_geq_some_factor = ForallInSet(
    a,
    Naturals,
    ForallInSet(b, Naturals, GreaterOrEqual(a * b, a).or_(GreaterOrEqual(a * b, b))),
).todo(_internal=True)
mul_positive_geq_factors = ForallInSet(
    a,
    Naturals,
    ForallInSet(
        b,
        Naturals,
        GreaterThan(a, 0)
        .and_(GreaterThan(b, 0))
        .implies(GreaterOrEqual(a * b, a).and_(GreaterOrEqual(a * b, b))),
    ),
).todo(_internal=True)
mul_of_factors_geq_1_is_gt_factors = ForallInSet(
    a,
    Naturals,
    ForallInSet(
        b,
        Naturals,
        GreaterThan(a, 1)
        .and_(GreaterThan(b, 1))
        .implies(GreaterThan(a * b, a).and_(GreaterThan(a * b, b))),
    ),
).todo(_internal=True)
prod_geq_some_factor = ForallInSet(
    s_seq,
    AllFiniteSequences,
    s_seq_set.is_subset_of(Naturals).implies(
        ExistsInSet(k, Naturals, GreaterOrEqual(prod_s_seq, s_k))
    ),
).todo(_internal=True)
prod_positive_geq_factors = ForallInSet(
    s_seq,
    AllFiniteSequences,
    s_seq_set.is_subset_of(Naturals)
    .and_(ForallInSet(k, Naturals, GreaterThan(s_k, 0)))
    .implies(ForallInSet(k, Naturals, GreaterOrEqual(Prod(s_seq), s_k))),
).todo(_internal=True)
prod_of_factors_geq_1_is_gt_factors = ForallInSet(
    s_seq,
    AllFiniteSequences,
    s_seq_set.is_subset_of(Naturals)
    .and_(ForallInSet(k, Naturals, GreaterThan(s_k, 1)))
    .implies(ForallInSet(k, Naturals, GreaterThan(prod_s_seq, s_k))),
).todo(_internal=True)

Naturals.theorems.product_theorems = Namespace(
    {
        "mul_divisible_by_factors": mul_divisible_by_factors,
        "mul_geq_some_factor": mul_geq_some_factor,
        "mul_positive_geq_factors": mul_positive_geq_factors,
        "mul_of_factors_geq_1_is_gt_factors": mul_of_factors_geq_1_is_gt_factors,
        "prod_geq_some_factor": prod_geq_some_factor,
        "prod_positive_geq_factors": prod_positive_geq_factors,
        "prod_of_factors_geq_1_is_gt_factors": prod_of_factors_geq_1_is_gt_factors,
        "prime_irreducible": prime_irreducible,
    }
)


def gt_implies_neq(set_):
    return ForallInSet(
        a,
        set_,
        ForallInSet(
            b,
            set_,
            GreaterThan(a, b).implies(neg(a.equals(b))),
        ),
    ).todo(_internal=True)


def lt_implies_neq(set_):
    return ForallInSet(
        a,
        set_,
        ForallInSet(
            b,
            set_,
            LessThan(a, b).implies(neg(a.equals(b))),
        ),
    ).todo(_internal=True)


def add_positive_gt_parts(set_):
    return ForallInSet(
        a,
        set_,
        ForallInSet(
            b,
            set_,
            GreaterThan(a, 0)
            .and_(GreaterThan(b, 0))
            .implies(GreaterThan(a + b, a).and_(GreaterThan(a + b, b))),
        ),
    ).todo(_internal=True)


Naturals.theorems.order_theorems = Namespace(
    {
        "gt_implies_neq": gt_implies_neq(Naturals),
        "lt_implies_neq": lt_implies_neq(Naturals),
        "add_positive_gt_parts": add_positive_gt_parts(Naturals),
        "prime_gt_1": prime_gt_1,
    }
)

Integers.theorems.order_theorems = Namespace(
    {
        "gt_implies_neq": gt_implies_neq(Integers),
        "lt_implies_neq": lt_implies_neq(Integers),
        "add_positive_gt_parts": add_positive_gt_parts(Integers),
    }
)

Rationals.theorems.root_2_irrational = root_2_irrational
Rationals.theorems.root_3_irrational = root_3_irrational
Rationals.theorems.cbrt_2_irrational = cbrt_2_irrational
Rationals.theorems.cbrt_3_irrational = cbrt_3_irrational
Rationals.theorems.prime_sqrt_irrational = prime_sqrt_irrational
Rationals.theorems.prime_cbrt_irrational = prime_cbrt_irrational

Rationals.theorems.order_theorems = Namespace(
    {
        "gt_implies_neq": gt_implies_neq(Rationals),
        "lt_implies_neq": lt_implies_neq(Rationals),
        "add_positive_gt_parts": add_positive_gt_parts(Rationals),
    }
)

Reals.theorems.order_theorems = Namespace(
    {
        "gt_implies_neq": gt_implies_neq(Reals),
        "lt_implies_neq": lt_implies_neq(Reals),
        "add_positive_gt_parts": add_positive_gt_parts(Reals),
    }
)

prime_or_composite = ForallInSet(
    p,
    Naturals,
    Naturals.prime(p).or_(neg(Naturals.prime(p))),
).todo(_internal=True)
neq_1_has_prime_divisor_nat = ForallInSet(
    k,
    Naturals,
    neg(Equals(k, 1)).implies(
        ExistsInSet(p, Naturals, Naturals.prime(p).and_(Naturals.divides(p, k)))
    ),
).todo(_internal=True)

gt_1_is_prod_primes = ForallInSet(
    k,
    Naturals,
    GreaterThan(k, 1).implies(
        ExistsInSet(
            s_seq,
            AllFiniteSequences,
            s_seq_set.is_subset_of(Naturals)
            .and_(ForallInSet(i, Naturals, Naturals.prime(s_i)))
            .and_(k.equals(prod_s_seq)),
        )
    ),
).todo(_internal=True)

Naturals.theorems.prime_theorems = Namespace(
    {
        "prime_divides_product": prime_divides_product,
        "prime_divides_power": prime_divides_power,
        "prime_or_composite": prime_or_composite,
        "neq_1_has_prime_divisor": neq_1_has_prime_divisor_nat,
        "gt_1_is_prod_primes": gt_1_is_prod_primes,
        "prime_neq_0": ForallInSet(
            p, Naturals, Naturals.prime(p).implies(neg(p.equals(0)))
        ).todo(_internal=True),
        "prime_neq_1": ForallInSet(
            p, Naturals, Naturals.prime(p).implies(neg(p.equals(1)))
        ).todo(_internal=True),
        "prime_gt_1": prime_gt_1,
        "prime_irreducible": prime_irreducible,
        "prime_irreducible_b": prime_irreducible_b,
        "prime_sqrt_irrational": prime_sqrt_irrational,
        "prime_cbrt_irrational": prime_cbrt_irrational,
        "root_2_irrational": root_2_irrational,
        "root_3_irrational": root_3_irrational,
        "cbrt_2_irrational": cbrt_2_irrational,
        "cbrt_3_irrational": cbrt_3_irrational,
    }
)
