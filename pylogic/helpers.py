import sympy as sp
from typing import Any, TYPE_CHECKING, TypedDict, Literal
from pylogic.proposition.proposition import Proposition
from pylogic.variable import Variable

if TYPE_CHECKING:
    from pylogic.symbol import Symbol
    from pylogic.set.sets import Set

    Term = Variable | Symbol | Set | sp.Basic | int | float
    Unification = dict[Variable, Term]


def replace(old: Term, new: Term, expr: Term) -> Term:
    if expr == old:
        return new
    elif isinstance(expr, sp.Basic):
        return expr.subs(old, new)
    else:
        return expr


def unify(
    a: Proposition | Term, b: Proposition | Term
) -> Unification | Literal[True] | None:
    """ """
    # a is the variable if at least one argument is a variable
    if isinstance(b, Variable):
        return unify(b, a)
    # Variable and Term
    if isinstance(a, Variable) and not isinstance(b, Proposition):
        return {a: b}
    # Term and Term
    if not isinstance(a, Proposition) and not isinstance(b, Proposition):
        return True if a == b else None
    # Proposition and Proposition
    if isinstance(a, Proposition) and isinstance(b, Proposition):
        return a.unify(b)
