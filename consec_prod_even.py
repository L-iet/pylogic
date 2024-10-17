from pylogic.helpers import assume
from pylogic.theories.natural_numbers import Naturals, zero
from pylogic.variable import Variable

n = Variable("n", natural=True)

zero_is_even = (
    (zero * (zero + 1))
    .equals(2 * zero)
    .by_simplification()
    .thus_there_exists("k", zero, Naturals, positions=[[1]])
)

induction_hypothesis = assume(Naturals.even(n * (n + 1)))

factor, n_times_nplus_1_is_2_times_factor = induction_hypothesis.extract()
step1 = ((n + 1) * (n + 2)).equals(n * (n + 1) + 2 * (n + 1)).by_simplification()
step2 = step1.p_substitute("right", n_times_nplus_1_is_2_times_factor[1])
step3 = (2 * factor + 2 * (n + 1)).equals(2 * (factor + (n + 1))).by_simplification()
step4 = step2.transitive(step3)
n_plus_1__times__n_plus_2__is_even = step4.thus_there_exists(
    "k", factor + (n + 1), Naturals
)
induction_step = n_plus_1__times__n_plus_2__is_even.followed_from(
    induction_hypothesis
).thus_forall(n, Naturals)
print(induction_step)


print(Naturals.weak_induction(zero_is_even, induction_step))

"""

"""
