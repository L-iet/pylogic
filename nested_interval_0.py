from pylogic.constant import Constant
from pylogic.helpers import assume
from pylogic.proposition.quantified.exists import ExistsInSet
from pylogic.proposition.quantified.forall import ForallInSet
from pylogic.proposition.relation.equals import Equals
from pylogic.structures.sequence import Sequence
from pylogic.structures.set_ import EmptySet, Intersection, Set
from pylogic.theories.natural_numbers import Naturals, one, zero
from pylogic.theories.real_analysis import Interval, Reals
from pylogic.variable import Variable

a = Sequence("a")
a.define_predicate(
    lambda n: Reals.contains(a[n]).and_(Reals.less_or_equal(a[n], a[n + 1]))
)

b = Sequence("b")
b.define_predicate(
    lambda n: Reals.contains(b[n]).and_(Reals.less_or_equal(b[n + 1], b[n]))
)

I = Sequence(
    "I", nth_term=lambda n: Interval(a[n], b[n], a_inclusive=True, b_inclusive=True)
)

x = Variable("x")
n = Variable("n")
k = Variable("k")

# this is assumed in the proof
# needed to ensure each interval is not empty
forall_n_in_N_an_leq_bn = ForallInSet(
    n, Naturals, Reals.less_or_equal(a[n], b[n]), is_assumption=True
)

A = Set(
    "A",
    predicate=lambda x: x.is_in(Reals).and_(ExistsInSet(n, Naturals, x.equals(a[n]))),
)

# proving that A is nonempty by showing that a0 is in A
a0 = a[zero]
a0_eq_a0 = Equals.reflexive(a0)
exists_n_in_naturals_a0_eq_n = a0_eq_a0.thus_there_exists(
    "n", zero, Naturals, positions=[[1]]
)
a0_is_real = a.predicate(0)[0]
a_predicate_for_0 = a0_is_real.p_and(exists_n_in_naturals_a0_eq_n)
a0_in_A = a0.is_in(A).by_predicate(a_predicate_for_0)
A_nonempty = a0_in_A.thus_not_empty()
# print(A_nonempty)

# proving that b0 is an upper bound for B
b0 = b[zero]
# using induction
# base case, b0 <= b0
b0_leq_b0 = Reals.less_or_equal.reflexive(b0)

# induction hypothesis, bn <= b0
n_in_N = assume(n.is_in(Naturals))
bn_leq_b0 = assume(Reals.less_or_equal(b[n], b0))

# induction step, now show that bn+1 <= b0
bnp1_leq_bn = b.predicate(n)[1]
bnp1_leq_b0 = bnp1_leq_bn.transitive(bn_leq_b0)
forall_n_bnp1_leq_b0 = bnp1_leq_b0.followed_from(bn_leq_b0).thus_forall(n_in_N)

# putting it all together, forall n in Naturals, bn <= b0
forall_n_in_N_bn_leq_b0 = Naturals.weak_induction(b0_leq_b0, forall_n_bnp1_leq_b0)

# using the above, we show that an <= b0 for all n in N
n_in_N = assume(n.is_in(Naturals))
forall_n_in_N_an_leq_b0 = (
    forall_n_in_N_an_leq_bn(n)
    .transitive(forall_n_in_N_bn_leq_b0(n))
    .thus_forall(n_in_N)
)

# now show that this is equivalent to b0 being an upper bound for A
x_in_A = x.is_in(A).assume()
n_in_N = n.is_in(Naturals).assume()
w_is_in_sequence_a = x_in_A.thus_predicate()[1]
k, k_in_N_and_w_eq_ak = w_is_in_sequence_a.extract()

ak_leq_b0 = forall_n_in_N_an_leq_b0(k)
w_leq_b0 = ak_leq_b0.substitute("left", k_in_N_and_w_eq_ak[1])
forall_w_in_A_w_leq_b0 = w_leq_b0.thus_forall(x_in_A)  # forall x in A, x <= b0

# therefore, A has an upper bound
b0_is_real = b.predicate(0)[0]
exists_real_ub_for_A = forall_w_in_A_w_leq_b0.thus_there_exists("ub", b0, Reals)

# by the completeness axiom, A has a least upper bound
A_has_lub = Reals.bounded_above_has_lub(A)(A_nonempty, exists_real_ub_for_A)
