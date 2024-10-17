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

# The proof esssentially goes as follows:

# 1. A is nonempty, since a0 is in A
# 2. bk is an upper bound for sequence a, and therefore set A = {a[n] | n in Naturals}
# 3. A has a least upper bound, lub_A
# 4. Given any k, a[k] <= lub_A <= b[k], so lub_A is in each interval I[k]

x = Variable("x")
n = Variable("n")
k = Variable("k")
k0 = Variable("k0")
k1 = Variable("k1")

# this is assumed in the proof
# needed to ensure each interval is not empty
forall_n_in_N_an_leq_bn = ForallInSet(
    n, Naturals, Reals.less_or_equal(a[n], b[n]), is_assumption=True
)

A = Set(
    "A",
    predicate=lambda x: x.is_in(Reals).and_(ExistsInSet(n, Naturals, x.equals(a[n]))),
)

# this can be proven by nested induction, but it's a bit long
forall_k_and_n_in_N_k_leq_n_implies_ak_leq_an_and_bn_leq_bk = ForallInSet(
    k0,
    Naturals,
    ForallInSet(
        k1,
        Naturals,
        Naturals.less_or_equal(k0, k1).implies(
            Reals.less_or_equal(a[k0], a[k1]).and_(Reals.less_or_equal(b[k1], b[k0]))
        ),
    ),
).todo()

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


bk = b[k]

# here, we prove that bk is an upper bound for A, so that we can show that A has a least upper bound
n_in_N, k_in_N = assume(n.is_in(Naturals), k.is_in(Naturals))
bk_is_real = b.predicate(k)[0]  # bk is a real number by definition of sequence b

# we do a proof by cases

# case 1: n <= k
n_leq_k = assume(Naturals.less_or_equal(n, k))
an_leq_ak = forall_k_and_n_in_N_k_leq_n_implies_ak_leq_an_and_bn_leq_bk(n, k)(n_leq_k)[
    0
]
ak_leq_bk = forall_n_in_N_an_leq_bn(k)
an_leq_bk = an_leq_ak.transitive(ak_leq_bk)
impl1 = an_leq_bk.followed_from(n_leq_k)

# case 2: k <= n
k_leq_n = assume(Naturals.less_or_equal(k, n))
an_leq_bn = forall_n_in_N_an_leq_bn(n)
bn_leq_bk = forall_k_and_n_in_N_k_leq_n_implies_ak_leq_an_and_bn_leq_bk(k, n)(k_leq_n)[
    1
]
an_leq_bk2 = an_leq_bn.transitive(bn_leq_bk)
impl2 = an_leq_bk2.followed_from(k_leq_n)

# strongly connected: for all naturals a,b, a<=b or b<=a
leq_is_strongly_connected = Naturals.order_is_strongly_connected(n, k)
an_leq_bk = leq_is_strongly_connected.by_cases(impl1, impl2)
forall_n_in_N_an_leq_bk = an_leq_bk.thus_forall(n_in_N)


# now show that this is equivalent to bk being an upper bound for A
x_in_A = x.is_in(A).assume()
n_in_N = n.is_in(Naturals).assume()
w_is_in_sequence_a = x_in_A.thus_predicate()[1]
i, i_in_N_and_w_eq_ai = w_is_in_sequence_a.extract()

ai_leq_bk = forall_n_in_N_an_leq_bk(i)
w_leq_bk = ai_leq_bk.substitute("left", i_in_N_and_w_eq_ai[1])
forall_w_in_A_w_leq_bk = w_leq_bk.thus_forall(x_in_A)  # forall w in A, w <= bk

# therefore, A has an upper bound
exists_real_ub_for_A = forall_w_in_A_w_leq_bk.thus_there_exists("ub", bk, Reals)

# by the completeness axiom, A has a least upper bound
A_has_lub = Reals.bounded_above_has_lub(A)(A_nonempty, exists_real_ub_for_A)
lub_A, lub_A_is_ub_and_least = A_has_lub.extract()
lub_A_is_real = lub_A_is_ub_and_least[0]
lub_A_is_ub = lub_A_is_ub_and_least[1]
lub_A_is_least = lub_A_is_ub_and_least[2]


# Given k, a[k] is a real number in A
ak = a[k]
ak_is_real = a.predicate(k)[0]
exists_n_in_N_ak_eq_an = Equals.reflexive(a[k]).thus_there_exists(
    "n", k, set_=Naturals, positions=[[1]]
)
ak_in_A = ak.is_in(A).by_predicate(ak_is_real.p_and(exists_n_in_N_ak_eq_an))

ak_leq_lub = lub_A_is_ub(ak)  # ak <= lub
bk_is_ub_for_A = forall_w_in_A_w_leq_bk.rename_variable("x")
if_bk_ub_then_lub_leq_bk = lub_A_is_least(bk)
lub_leq_bk = bk_is_ub_for_A.modus_ponens(if_bk_ub_then_lub_leq_bk)  # lub <= bk

# therefore, lub is in each interval I[k]
lub_in_int_k = lub_A_is_real.p_and(ak_leq_lub, lub_leq_bk)

Ik_eval = I[k].evaluate()
Ik_is_interval = I[k].equals(Ik_eval).by_simplification()  # [a[k], b[k]] = I[k]
lub_in_Ik_eval = lub_A.is_in(Ik_eval).by_predicate(lub_in_int_k)

lub_in_Ik = lub_in_Ik_eval.substitute("left", Ik_is_interval)
forall_k_lub_in_Ik = lub_in_Ik.thus_forall(k_in_N)


intersection = Intersection(I, name="I")
print(lub_A.is_in(intersection).by_predicate(forall_k_lub_in_Ik))
