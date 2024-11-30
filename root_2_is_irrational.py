from pylogic.assumptions_context import AssumptionsContext, conclude
from pylogic.expressions.expr import sqrt
from pylogic.proposition.not_ import Not
from pylogic.theories.numbers import Integers, Naturals, Rationals

root_2 = rt2 = sqrt(2)


with AssumptionsContext() as ctx:
    rt2_rational = root_2.is_in(Rationals).assume()

    rt2_ratio = Rationals.theorems.ratio_of_integers_lowest_terms(rt2)
    p, (_, (q, (_, _, rt2_eq_p_over_q, gcd_p_q_eq_1))) = rt2_ratio

    two_prime = Naturals.prime(2).by_inspection()

    p2_eq_2q2 = ((rt2_eq_p_over_q**2) * q**2).evaluate().symmetric()
    two_div_p2, _ = Integers.theorems.division_theorems.product(p**2, 2, q**2)(
        p2_eq_2q2
    )
    two_div_p = Integers.theorems.division_theorems.prime.prime_divides_power(2, p, 2)(
        two_prime, two_div_p2
    )

    k, (_, p_eq_2k) = two_div_p.definition.rename_variable("k")  # p = 2k
    q2_eq_2k2 = (p_eq_2k**2).substitute("right", p2_eq_2q2) / 2
    q2_eq_2k2 = q2_eq_2k2.evaluate()

    two_div_q2, _ = Integers.theorems.division_theorems.product(q**2, 2, k**2)(
        q2_eq_2k2
    )
    two_div_q = Integers.theorems.division_theorems.prime.prime_divides_power(2, q, 2)(
        two_prime, two_div_q2
    )

    two_div_gcd_p_q = Integers.theorems.division_theorems.gcd(2, p, q)(
        two_div_p, two_div_q
    )
    two_div_1 = two_div_gcd_p_q.substitute("right", gcd_p_q_eq_1)
    two_not_div_1 = Not(Integers.divides(2, 1)).by_inspection()
    contra = two_div_1.contradicts(two_not_div_1)
    conclude(contra)

print(ctx.get_proven()[0])
