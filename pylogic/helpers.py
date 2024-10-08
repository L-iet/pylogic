from __future__ import annotations

from decimal import Decimal
from enum import Enum
from fractions import Fraction
from typing import (
    TYPE_CHECKING,
    Any,
    Callable,
    Iterable,
    Literal,
    TypeVar,
    TypeVarTuple,
    overload,
)

from pylogic.expressions.expr import Expr
from pylogic.expressions.expr import replace as _replace
from pylogic.proposition.proposition import Proposition
from pylogic.symbol import Symbol
from pylogic.variable import Variable

T = TypeVar("T")
P = TypeVar("P", bound=Proposition)
Ps = TypeVarTuple("Ps")

if TYPE_CHECKING:
    from pylogic import Term, Unification
    from pylogic.constant import Constant
    from pylogic.structures.class_ import Class
    from pylogic.structures.set_ import Set


def replace(expr, old, new, equal_check: Callable | None = None) -> Any:
    return _replace(expr, old, new, equal_check=equal_check)


def get_vars(expr: Any) -> set[Variable]:
    """
    Get all variables in expr.
    """
    if isinstance(expr, Variable):
        return {expr}
    if hasattr(expr, "variables"):
        return expr.variables
    return set()


def get_consts(expr: Any) -> set[Constant]:
    from pylogic.constant import Constant

    """
    Get all constants in expr.
    """
    if isinstance(expr, Constant):
        return {expr}
    if is_numeric(expr):
        return {Constant(expr)}
    if hasattr(expr, "constants"):
        return expr.constants
    return set()


def get_sets(expr: Any) -> set[Set]:
    """
    Get all sets in expr.
    """
    from pylogic.structures.set_ import Set

    if isinstance(expr, Set):
        return {expr}
    if hasattr(expr, "sets"):
        return expr.sets
    return set()


def get_class_ns(expr: Any) -> set[Class]:
    """
    Get all class namespaces in expr.
    """
    if (
        expr.__class__.__name__.startswith("Collection")
        and expr.__class__.__name__[10].isdigit()
    ):
        return {expr}
    if hasattr(expr, "class_ns"):
        return expr.class_ns
    return set()


def deepcopy(obj: T) -> T:
    """
    Creates a deep copy of the object if object is not numeric.

    Raises
    ------
    AttributeError "obj has no attribute deepcopy" if obj is neither numeric nor a pylogic object.
    """
    if is_numeric(obj):
        return obj
    return obj.deepcopy()  # type: ignore


def copy(obj: T) -> T:
    """
    Creates a shallow copy of the object if object is not numeric.

    Raises
    ------
    AttributeError "obj has no attribute copy" if obj is neither numeric nor a pylogic object.
    """
    if is_numeric(obj):
        return obj
    return obj.copy()  # type: ignore


def try_except(
    func: Callable[..., T],
    exc_to_ignore: tuple[Exception, ...] = (),
    exc_to_raise: Exception | None = None,
    cleanup: Callable[[], None] | None = None,
    *args: Any,
    **kwargs: Any,
) -> T | None:
    """
    Try to run a function and return the result if successful.
    If any of exc_to_ignore is encountered, raise exc_to_raise
    (if exc_to_raise not None) or return None (if None).
    If exc_to_ignore is empty, it raises all exceptions.
    """
    if cleanup is None:
        cleanup = lambda: None
    try:
        return func(*args, **kwargs)
    except exc_to_ignore:  # type: ignore
        if exc_to_raise is not None:
            raise exc_to_raise
        return None
    finally:
        cleanup()


def eval_same(x: Any, y: Any) -> bool:
    """
    Check if x and y evaluate to the same value.
    """
    from pylogic.structures.set_ import Set

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


@overload
def find_first(predicate: Callable[[T], bool], args: Iterable[T]) -> tuple[int, T]: ...
@overload
def find_first(
    predicate: Callable[[T], bool], args: Iterable[T]
) -> tuple[None, None]: ...
def find_first(
    predicate: Callable[[T], bool], args: Iterable[T]
) -> tuple[int, T] | tuple[None, None]:
    """
    Find the first element in args that satisfies the predicate.
    """
    new_pred = lambda x: predicate(x[1])
    return next(filter(new_pred, enumerate(args)), (None, None))


@overload
def assume(arg: P) -> P: ...
@overload
def assume(arg: P, *args: *Ps) -> tuple[P, *Ps]: ...
def assume(arg: P, *args: *Ps) -> P | tuple[P, *Ps]:
    all_args = (arg, *args)
    for argmnt in all_args:
        argmnt._set_is_assumption(True)  # type: ignore
    if len(all_args) == 1:
        return arg
    return all_args


def latex(arg: Any) -> str:
    # TODO: Add support for Function
    from pylogic.expressions.expr import Expr
    from pylogic.proposition.proposition import Proposition
    from pylogic.structures.set_ import Set
    from pylogic.symbol import Symbol

    if isinstance(arg, (Expr, Symbol, Set, Proposition)):
        return arg._latex()
    return f"{{{str(arg)}}}"


class Side(Enum):
    LEFT = 1
    RIGHT = 2

    def __invert__(self):
        if self == Side.LEFT:
            return Side.RIGHT
        else:
            return Side.LEFT
