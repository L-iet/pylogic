from pylogic import *

theorems = Integers.theorems.division_theorems
rt2 = sqrt(2)
two_prime = Naturals.prime(2).by_inspection()

def two_divides_x(x, y, xsquared_equals_2_ysquared):
    two_div_x2, _ = theorems.mul(x**2, 2, y**2)(xsquared_equals_2_ysquared)
    return theorems.prime.prime_divides_power(2, x, 2)(two_prime, two_div_x2)

with AssumptionsContext() as ctx:
    rt2_rational = rt2.is_in(Rationals).assume()
    rt2_ratio = Rationals.theorems.ratio_of_integers_lowest_terms(rt2)
    p, (_, (q, (_, _, rt2_eq_p_over_q, gcd_p_q_eq_1))) = rt2_ratio

    p2_eq_2q2 = ((rt2_eq_p_over_q**2) * q**2).evaluate().symmetric()
    two_div_p = two_divides_x(p, q, p2_eq_2q2)
    k, (_, p_eq_2k) = two_div_p.definition.rename_variable("k")
    q2_eq_2k2 = (p_eq_2k**2).substitute("right", p2_eq_2q2) / 2
    q2_eq_2k2 = q2_eq_2k2.evaluate()

    two_div_q = two_divides_x(q, k, q2_eq_2k2)
    two_div_gcd_p_q = theorems.gcd(2, p, q)(two_div_p, two_div_q)
    two_div_1 = two_div_gcd_p_q.substitute("right", gcd_p_q_eq_1)
    two_not_div_1 = Not(Integers.divides(2, 1)).by_inspection()
    contradiction = two_div_1.contradicts(two_not_div_1)

ctx.get_first_proven()
