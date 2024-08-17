from __future__ import annotations
from typing import Any, TYPE_CHECKING, Literal, Iterable, Callable, TypeVar
from pylogic.proposition.proposition import Proposition
from pylogic.variable import Variable
from pylogic.expressions.expr import Expr, replace as _replace

T = TypeVar("T")

if TYPE_CHECKING:
    from fractions import Fraction
    from pylogic.symbol import Symbol
    from pylogic.structures.sets import Set
    from sympy import Basic

    Numeric = Fraction | int | float
    PBasic = Symbol | Numeric
    Unevaluated = Symbol | Set | Expr
    Term = Unevaluated | Numeric | Basic
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
    # Expr and Expr
    if isinstance(a, Expr) and isinstance(b, Expr):
        return a.unify(b)
    # Term and Term
    if not isinstance(a, Proposition) and not isinstance(b, Proposition):
        return True if a == b else None
    # Proposition and Proposition
    if isinstance(a, Proposition) and isinstance(b, Proposition):
        return a.unify(b)


def type_check(arg: Any, *types: type, context: Any = None) -> Literal[True]:
    """Check if arg is an instance of any of the types.

    Raises TypeError if arg is not an instance of any of the types.
    """
    if isinstance(arg, types):
        return True
    msg = f"Expected {types} but got {type(arg)}"
    if context:
        msg += f" in {context}"
    raise TypeError(msg)


def find_first(predicate: Callable[[T], bool], args: Iterable[T]) -> T | None:
    for arg in args:
        if predicate(arg):
            return arg
    return None


def assume(*args: Proposition) -> Proposition | tuple[Proposition, ...]:
    for arg in args:
        arg.is_assumption = True
    if len(args) == 1:
        return args[0]
    return args
