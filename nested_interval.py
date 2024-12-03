from pylogic.assumptions_context import AssumptionsContext, conclude, ctx_var
from pylogic.constant import Constant
from pylogic.enviroment_settings.settings import settings
from pylogic.helpers import assume
from pylogic.proposition.quantified.exists import ExistsInSet
from pylogic.proposition.quantified.forall import ForallInSet
from pylogic.proposition.relation.equals import Equals
from pylogic.structures.sequence import Sequence
from pylogic.structures.set_ import EmptySet, Intersection, SeqSet, Set
from pylogic.theories.numbers import Naturals, one, zero
from pylogic.theories.real_numbers import Reals, interval
from pylogic.variable import Variable

settings["PYTHON_OPS_RETURN_PROPS"] = True

a = Sequence("a", real=True)
b = Sequence("b", real=True)

I = Sequence(
    "I",
    nth_term=lambda n: interval(
        [a[n], b[n]],
    ),
)

# The proof esssentially goes as follows:

# 1. A is nonempty, since a0 is in A
# 2. bk is an upper bound for sequence a, and therefore set A = {a[n] | n in Naturals}
# 3. A has a least upper bound, lub_A
# 4. Given any k, a[k] <= lub_A <= b[k], so lub_A is in each interval I[k]

n = Variable("n")
k0 = Variable("k0")
k1 = Variable("k1")

forall_n_in_N_an_leq_bn = ForallInSet(n, Naturals, a[n] <= b[n]).assume()
forall_k_and_n_in_N_k_leq_n_implies_ak_leq_an_and_bn_leq_bk = ForallInSet(
    k0,
    Naturals,
    ForallInSet(
        k1, Naturals, (k0 <= k1).implies((a[k0] <= a[k1]).and_(b[k1] <= b[k0]))
    ),
).assume()

A = SeqSet(a)

# Part 1: A is nonempty
# proving that A is nonempty by showing that a0 is in A
a0 = a[zero]
a0_in_A = a0.is_in(A).by_inspection()
A_nonempty = a0_in_A.thus_not_empty()


# Part 2: bk is an upper bound for set A
# here, we prove that bk is an upper bound for A, so that we can show that A has a least upper bound
# proving that an <= bk for all n and k in Naturals
with AssumptionsContext() as ctx:
    k = ctx_var("k", natural=True)
    bk = b[k]
    ak = a[k]
    Ik = I[k]

    # given any x in A, we show that x <= bk
    with AssumptionsContext() as x_ctx:
        x = ctx_var("x")
        x_in_A = x.is_in(A).assume()
        n, (_, x_eq_an) = x_in_A.thus_predicate().rename_variable("n")
        an = x_eq_an.right

        # we do a proof by cases

        # case 1: n <= k
        with AssumptionsContext() as ctx2:
            n_leq_k = assume(n <= k)
            an_leq_ak = forall_k_and_n_in_N_k_leq_n_implies_ak_leq_an_and_bn_leq_bk(
                n, k
            )(n_leq_k)[0]
            ak_leq_bk = forall_n_in_N_an_leq_bn(k)
            an_leq_bk = an_leq_ak.transitive(ak_leq_bk)
            conclude(an_leq_bk)
        impl1 = ctx2.get_proven()[0]

        with AssumptionsContext() as ctx2:
            # case 2: k <= n
            k_leq_n = assume(k <= n)
            an_leq_bn = forall_n_in_N_an_leq_bn(n)
            bn_leq_bk = forall_k_and_n_in_N_k_leq_n_implies_ak_leq_an_and_bn_leq_bk(
                k, n
            )(k_leq_n)[1]
            an_leq_bk2 = an_leq_bn.transitive(bn_leq_bk)
            conclude(an_leq_bk2)
        impl2 = ctx2.get_proven()[0]

        # strongly connected: for all naturals a,b, a<=b or b<=a
        leq_is_strongly_connected = Naturals.order_is_strongly_connected(n, k)
        an_leq_bk = leq_is_strongly_connected.by_cases(impl1, impl2)
        conclude(an_leq_bk.substitute("left", x_eq_an))

    forall_x_in_A_x_leq_bk = x_ctx.get_proven()[0]
    # therefore, A has an upper bound
    exists_real_ub_for_A = forall_x_in_A_x_leq_bk.thus_there_exists("ub", bk, Reals)

    # by the completeness axiom, A has a least upper bound
    A_has_lub = Reals.bounded_above_has_lub(A)(A_nonempty, exists_real_ub_for_A)
    lub_A, lub_A_is_ub_and_least = A_has_lub.extract()
    lub_A_is_real = lub_A_is_ub_and_least[0]
    lub_A_is_ub = lub_A_is_ub_and_least[1]
    lub_A_is_least = lub_A_is_ub_and_least[2]

    ak_leq_lub = lub_A_is_ub(ak)
    if_bk_ub_then_lub_leq_bk = lub_A_is_least(bk)
    lub_leq_bk = forall_x_in_A_x_leq_bk.modus_ponens(if_bk_ub_then_lub_leq_bk)

    lub_in_interval_k = lub_A_is_real.and_(ak_leq_lub, lub_leq_bk)

    Ik_eval = Ik.evaluate()
    Ik_eq_interval = Ik.equals(Ik_eval).by_simplification()  # [a[k], b[k]] = I[k]
    lub_in_Ik_eval = lub_A.is_in(Ik_eval).by_predicate(lub_in_interval_k)
    lub_in_Ik = lub_in_Ik_eval.substitute("left", Ik_eq_interval)
    conclude(lub_in_Ik)

intersection = Intersection(I, name="I")

forall_k_lub_in_Ik = ctx.get_proven()[0]
print(lub_A.is_in(intersection).by_predicate(forall_k_lub_in_Ik))
