from __future__ import annotations
from decimal import Decimal
from enum import Enum
from typing import (
    Any,
    TYPE_CHECKING,
    Literal,
    Iterable,
    Callable,
    TypeVar,
    overload,
    TypeVarTuple,
)
from pylogic.proposition.proposition import Proposition
from pylogic.variable import Variable
from pylogic.symbol import Symbol
from pylogic.structures.set_ import Set
from pylogic.expressions.expr import Expr, replace as _replace

T = TypeVar("T")
P = TypeVar("P", bound=Proposition)
Ps = TypeVarTuple("Ps")

if TYPE_CHECKING:
    from fractions import Fraction
    from sympy import Basic

    Numeric = Fraction | int | float
    PBasic = Symbol | Numeric
    Unevaluated = Symbol | Set | Expr
    Term = Unevaluated | Numeric | Basic
    Unification = dict[Variable, Term]


def replace(expr, old, new) -> Any:
    return _replace(expr, old, new)


def eval_same(x: Any, y: Any) -> bool:
    """
    Check if x and y evaluate to the same value.
    """
    if isinstance(x, (Symbol, Set, Expr)):
        return x.eval_same(y)
    if isinstance(y, (Symbol, Set, Expr)):
        return eval_same(y, x)
    return x == y


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


def is_numeric(arg: Any) -> bool:
    return isinstance(arg, (int, float, Fraction, complex, Decimal))


def find_first(predicate: Callable[[T], bool], args: Iterable[T]) -> T | None:
    for arg in args:
        if predicate(arg):
            return arg
    return None


@overload
def assume(arg: P) -> P: ...
@overload
def assume(arg: P, *args: *Ps) -> tuple[P, *Ps]: ...
def assume(arg: P, *args: *Ps) -> P | tuple[P, *Ps]:
    all_args = (arg, *args)
    for argmnt in all_args:
        argmnt.is_assumption = True  # type: ignore
    if all_args == 1:
        return arg
    return all_args


class Side(Enum):
    LEFT = 1
    RIGHT = 2

    def __invert__(self):
        if self == Side.LEFT:
            return Side.RIGHT
        else:
            return Side.LEFT
