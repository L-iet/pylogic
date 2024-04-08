from pylogic.proposition.proposition import Proposition
from pylogic.proposition.quantified.forall import Forall
from pylogic.proposition.ordering.greaterthan import GreaterThan
from pylogic.proposition.ordering.lessthan import LessThan
from pylogic import p_symbol as ps
from pylogic.variable import Variable
import sympy as sp


# print(sys.path)
p = Proposition
x = Variable("x", real=True)
Px = Proposition("P", args=[x])
Py = p("P", args=[ps.Symbol("y", real=True)])
Q = p("Q")
R = p("R")
S = p("S")
T = p("T")
forallXPx = Forall(x, Px, is_assumption=True)

# print(Py, forallXPx)
py = Py.is_special_case_of(forallXPx)
print(py.is_proven)

print(x.is_integer)
eps = Variable("eps", real=True)
eps_positive = GreaterThan(eps, 0, is_assumption=True)
absolute_x_positive = GreaterThan.is_absolute(sp.Abs(x))
root_eps_positive = GreaterThan.is_rational_power(sp.sqrt(eps), eps_positive)
absx_lt_sqrt_eps = LessThan(sp.Abs(x), sp.sqrt(eps), is_assumption=True)
xsq_lt_eps_t_absx = absx_lt_sqrt_eps.p_multiply_by_positive(
    abs(x), GreaterThan.is_absolute(abs(x))
)
eps_t_absx_lt_eps = absx_lt_sqrt_eps.p_multiply_by_positive(
    sp.sqrt(eps), root_eps_positive
)
xsq_lt_eps = xsq_lt_eps_t_absx.transitive(eps_t_absx_lt_eps)
x_squared_is_continuous = (
    xsq_lt_eps.followed_from(absx_lt_sqrt_eps)
    .p_and_reverse(root_eps_positive)
    .thus_there_exists("delta", sp.sqrt(eps))
    .followed_from(eps_positive)
    .thus_forall(eps)
    .thus_forall(x)
)

# TODO
# Option 1: Implement a way to determine what equations need to hold for two propositions
# to be equivalent

print(x_squared_is_continuous, x_squared_is_continuous.is_proven)
