from __future__ import annotations
from typing import Any, TYPE_CHECKING, TypedDict, Literal
from pylogic.proposition.proposition import Proposition
from pylogic.variable import Variable
from pylogic.expressions.expr import Expr, replace as _replace

if TYPE_CHECKING:
    from pylogic.symbol import Symbol
    from pylogic.structures.sets import Set

    Term = Symbol | Set | Expr | int | float
    Unification = dict[Variable, Term]


def replace(expr, old, new) -> Any:
    return _replace(expr, old, new)


# TODO: Change unification so that we cannot prove
# P(x) from forall x: P(1).
def unify(
    a: Proposition | Term, b: Proposition | Term
) -> Unification | Literal[True] | None:
    """Unification algorithm."""
    # a is the variable if at least one argument is a variable
    if isinstance(b, Variable) and not isinstance(a, Variable):
        return unify(b, a)
    # Variable and Term
    if isinstance(a, Variable) and not isinstance(b, Proposition):
        return True if a == b else {a: b}
    # Term and Term
    if not isinstance(a, Proposition) and not isinstance(b, Proposition):
        return True if a == b else None
    # Proposition and Proposition
    if isinstance(a, Proposition) and isinstance(b, Proposition):
        return a.unify(b)
