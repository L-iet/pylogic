from pylogic.proposition.and_ import And
from pylogic.proposition.proposition import Proposition
from pylogic.proposition.quantified.forall import Forall, ForallInSet
from pylogic.proposition.quantified.exists import ExistsInSet
from pylogic.proposition.ordering.greaterthan import (
    GreaterThan,
    is_absolute,
    is_rational_power,
)
from pylogic.proposition.ordering.lessthan import LessThan
from pylogic.proposition.relation.equals import Equals
from pylogic.proposition.or_ import Or
from pylogic.proposition.exor import ExOr
from pylogic.proposition.ordering.theorems import (
    order_axiom_bf,
    absolute_value_nonnegative_f,
)
from pylogic.proposition.not_ import Not, neg, are_negs
from pylogic.constant import Constant
from pylogic.variable import Variable
from pylogic.structures.sets import Naturals0, Reals, Set
from pylogic.expressions.expr import sqrt, sub, add
from pylogic.expressions.abs import Abs

printing = False


def log(*args, **kwargs):
    if printing:
        print(*args, **kwargs)


x = Variable("x", real=True)
xnot0: Not[Equals] = neg(Equals(Abs(x), 0), True)

Px = Proposition("P", args=[x])
Py = Proposition("P", args=[Constant("y", real=True)])
forallXPx = Forall(x, Px, is_assumption=True)

# log(Py, forallXPx)
py = Py.is_special_case_of(forallXPx)
log(py.is_proven)  # True

### proof that lim_x->0 x^2 = 0

eps = Variable("eps", real=True)
eps_positive = GreaterThan(eps, 0, is_assumption=True)

absolute_x_positive = is_absolute(Abs(x), xnot0)
root_eps_positive = is_rational_power(sqrt(eps), eps_positive)
absx_lt_sqrt_eps = LessThan(Abs(x), sqrt(eps), is_assumption=True)
xsq_lt_eps_t_absx = absx_lt_sqrt_eps.p_multiply_by_positive(
    Abs(x), is_absolute(Abs(x), xnot0)
)
eps_t_absx_lt_eps = absx_lt_sqrt_eps.p_multiply_by_positive(
    sqrt(eps), root_eps_positive
)
xsq_lt_eps = xsq_lt_eps_t_absx.transitive(eps_t_absx_lt_eps)
lim_x_sq_at_0 = (
    xsq_lt_eps.followed_from(absx_lt_sqrt_eps)
    .p_and_reverse(root_eps_positive)
    .thus_there_exists("delta", sqrt(eps), [[0], [1, 0]])
    .followed_from(eps_positive)
    .thus_forall(eps)
    .thus_forall(x)
)
# note that we also assumed that |x| != 0 above

# forall x: forall eps: [eps > 0 -> exists delta: (delta > 0 /\ [Abs(x) < delta -> x**2 < delta**2])] True
log(lim_x_sq_at_0.is_proven)

###  Proving Theorem 1.2.6 (the converse statement) Understanding Analysis, 2nd Edition
printing = False
# if (forall eps>0, |a-b|<eps) then a = b
a = Constant("a", real=True)
b = Constant("b", real=True)
abs_a_minus_b = Abs(a - b)  # type: ignore

# We assume forall eps, eps > 0 => |a-b| < eps
premise = Forall(
    eps, GreaterThan(eps, 0).implies(LessThan(abs_a_minus_b, eps)), is_assumption=True
)
premise2 = premise.in_particular(abs_a_minus_b)

# ~ |a-b| > 0
abs_a_minus_b_is_not_pos: Not[GreaterThan] = (
    Equals(abs_a_minus_b, abs_a_minus_b)
    .by_simplification()
    .modus_ponens(order_axiom_bf(abs_a_minus_b, abs_a_minus_b))
    .modus_tollens(premise2)
)

disj = absolute_value_nonnegative_f(a - b)
# |a-b| = 0
abs_a_minus_b_is_0: Equals = disj.unit_resolve(abs_a_minus_b_is_not_pos)  # type: ignore
log(neg(disj.propositions[0]) in {abs_a_minus_b_is_not_pos})
# a-b = 0
res = abs_a_minus_b_is_0.zero_abs_is_0()
# need a tactic to convert this to a=b

log(res.from_assumptions)

##############################

printing = False
y = Constant("y")
z = Variable("z")

Pxy = Proposition("P", args=[x, y])
Qxz = Proposition("Q", args=[x, z])
Ryz = Proposition("R", args=[y, z])
Wxy = Proposition("W", args=[x, y])
p = Forall(x, Or(And(Pxy.implies(Qxz), Ryz), Wxy))
q = Forall(
    x,
    Or(
        And(Proposition("P", args=[2, y]).implies(Proposition("Q", args=[2, z])), Ryz),
        Proposition("W", args=[2, Variable("y")]),
    ),
)
log(p.unify(q))
###############################
printing = False
a = Forall(x, And(Px, Qxz))
log(a.de_morgan().de_morgan())
###############################
printing = False
from pylogic.proposition.relation.contains import IsContainedIn
from pylogic.theories.arithmetic import weak_induction


n = Variable("n", integer=True, positive=True)

bc = GreaterThan(1, 0).by_inspection()
istep = Forall(
    n,
    IsContainedIn(n, Naturals0)
    .and_(GreaterThan(add(n, 1), 0))
    .implies(GreaterThan(add(n, 2), 0)),
    is_assumption=True,
)

log(weak_induction(bc, istep).as_text())

###############################
printing = False

P = Proposition("P")
np = neg(P, is_assumption=True)
Q = Proposition("Q", is_assumption=True)
R = Proposition("R")
QImpP = Q.implies(P, is_assumption=True)

log(Q.modus_ponens(QImpP).contradicts(np).thus_assumptions_cannot_all_hold())

###############################
printing = False
P = Proposition("P")
Q = Proposition("Q")
R = Proposition("R")
S = Proposition("S")
a = P.and_(Q, R).implies(S, is_assumption=True)
b = P.and_(Q, is_assumption=True)
p = P.is_one_of(b)
# log(a.unit_definite_clause_resolve(p))


###############################
printing = False
P = Proposition("P", is_assumption=True)
Q = Proposition("Q")
R = Proposition("R")
S = Proposition("S")

a = ExOr(P, Q, R, S, is_assumption=True)
log(a.unit_resolve(np))

###############################
printing = False
Px = Proposition("P", args=[x])
r = Constant("r", real=True)
s = Constant("s")
a = ForallInSet(x, Reals, Px, is_assumption=True)
log(a.in_particular(r))  # good
# a.in_particular(eps)  # eps is a variable, bad
# a.in_particular(s)  # s is not real, bad
###############################
printing = False
a = ExistsInSet(x, Reals, Px, is_assumption=True)
c, Pc = a.extract()
log(c, Pc)
###############################
printing = False
ub = Constant("ub", real=True)
s = Set("S")
is_ub = lambda ub, s: ForallInSet(
    x,
    s,
    GreaterThan(ub, x).or_(Equals(ub, x)),
    description=f"{ub} is an upper bound of {s}",
)
lub = Variable("lub", real=True)
has_lub = lambda s: ExistsInSet(
    lub,
    Reals,
    is_ub(lub, s).and_(
        ForallInSet(
            z,
            Reals,
            is_ub(z, s).implies(LessThan(z, lub).or_(Equals(z, lub))),
        )
    ),
)
log(has_lub(s).describe())
###############################
printing = False

p = Proposition("P", is_assumption=True)
pImpq = p.implies(Proposition("Q"), is_assumption=True)
q = Proposition("Q")
r = Proposition("R")
a = p.modus_ponens(pImpq).followed_from(p, pImpq)
log(a)
log(p.is_assumption, pImpq.is_assumption)

###############################

from pylogic.theories.real_analysis import *
