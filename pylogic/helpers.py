from __future__ import annotations

from decimal import Decimal
from enum import Enum
from fractions import Fraction
from functools import wraps
from types import SimpleNamespace
from typing import (
    TYPE_CHECKING,
    Any,
    Callable,
    Container,
    Generic,
    Iterable,
    Literal,
    TypeVar,
    TypeVarTuple,
    overload,
)

from pylogic.expressions.expr import Expr
from pylogic.expressions.expr import replace as _replace

T = TypeVar("T")
U = TypeVar("U")
E = TypeVar("E", bound=Expr)

Ps = TypeVarTuple("Ps")
TNumeric = TypeVar("TNumeric", bound=int | float | Fraction | complex | Decimal)

if TYPE_CHECKING:
    from pylogic.constant import Constant
    from pylogic.expressions.sequence_term import SequenceTerm
    from pylogic.proposition.proposition import Proposition
    from pylogic.structures.class_ import Class
    from pylogic.structures.sequence import Sequence
    from pylogic.structures.set_ import Set
    from pylogic.symbol import Symbol
    from pylogic.typing import PythonNumeric, Term, Unification
    from pylogic.variable import Variable

    P = TypeVar("P", bound=Proposition)
    TSet = TypeVar("TSet", bound=Set)
    TSequence = TypeVar("TSequence", bound=Sequence)
    S = TypeVar("S", bound=Symbol)
else:
    TSet = TypeVar("TSet")
    TSequence = TypeVar("TSequence")
    S = TypeVar("S")


def fn_alias(orig_func: Callable[..., T], new_name: str) -> Callable[..., T]:
    """
    Creates a function alias for the original function.

    This is useful for creating a function that has almost the same docstring
    as the original function, but with a different name.

    Should not be used as a decorator.

    Parameters
    ----------
    orig_func : Callable
        The original function to create an alias for.
    new_name : str
        The new name for the function.

    Returns
    -------
    Callable
        A function that is an alias for the original function.
    """

    # so that documentation tools get the correct signature
    @wraps(orig_func)
    def new_func(*args: Any, **kwargs: Any) -> T:
        return orig_func(*args, **kwargs)

    new_doc = orig_func.__doc__ and orig_func.__doc__.replace(
        orig_func.__name__, new_name
    )
    new_func.__doc__ = new_doc and (
        f"Alias for :py:func:`{orig_func.__name__}`.\n" + new_doc
    )
    new_func.__name__ = new_name

    return new_func


def replace(
    expr,
    replace_dict: dict,
    equal_check: Callable | None = None,
    positions: list[list[int]] | None = None,
) -> Any:
    return _replace(expr, replace_dict, equal_check=equal_check, positions=positions)


def get_vars(expr: Any) -> set[Variable]:
    """
    Get all variables in expr.
    """
    from pylogic.variable import Variable

    if isinstance(expr, Variable):
        return {expr}
    return getattr(expr, "variables", set())


def get_consts(expr: Any) -> set[Constant]:
    from pylogic.constant import Constant

    """
    Get all constants in expr.
    """
    if isinstance(expr, Constant):
        return {expr}
    if is_python_numeric(expr):
        return {Constant(expr)}
    return getattr(expr, "constants", set())


def get_sets(expr: Any) -> set[Set]:
    """
    Get all sets in expr.
    """
    from pylogic.structures.set_ import Set

    if isinstance(expr, Set):
        return {expr}
    return getattr(expr, "sets", set())


def get_class_ns(expr: Any) -> set[Class]:
    """
    Get all class{n} in expr.
    """
    if (
        expr.__class__.__name__.startswith("Collection")
        and expr.__class__.__name__[10].isdigit()
    ):
        return {expr}
    return getattr(expr, "class_ns", set())


def deepcopy(obj: T) -> T:
    """
    Creates a deep copy of the object if object is not numeric.

    Raises
    ------
    AttributeError "obj has no attribute deepcopy" if obj is neither numeric nor a pylogic object.
    """
    if is_python_numeric(obj):
        return obj
    return obj.deepcopy()  # type: ignore


def copy(obj: T) -> T:
    """
    Creates a shallow copy of the object if object is not numeric.

    Raises
    ------
    AttributeError "obj has no attribute copy" if obj is neither numeric nor a pylogic object.
    """
    if is_python_numeric(obj):
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
    from pylogic.symbol import Symbol

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
    from pylogic.proposition.proposition import Proposition
    from pylogic.variable import Variable

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


def type_check_no(arg: Any, *types: type, context: Any = None) -> Literal[True]:
    """Assert that arg is not an instance of any of the types.

    Raises TypeError if arg is an instance of any of the types.
    """
    msg = f"Did not expect {types} but got {type(arg)}"
    if context:
        msg += f" in {context}"
    if isinstance(arg, types):
        raise TypeError(msg)
    return True


def is_python_numeric(*args: Any) -> bool:
    """
    Check if the arguments are of Python numeric types.
    """
    return all(
        isinstance(arg, (int, float, Fraction, complex, Decimal)) for arg in args
    )


def is_numeric(*args: Any) -> bool:
    """
    Check if the arguments are of numeric types.
    """
    from pylogic.constant import Constant

    def check(arg):
        if isinstance(arg, Constant):
            arg = arg.value
        return isinstance(arg, (int, float, Fraction, complex, Decimal))

    return all(check(arg) for arg in args)


def is_python_real_numeric(*args: Any) -> bool:
    """
    Check if the arguments are of Python real numeric types.
    """
    return all(isinstance(arg, (int, float, Fraction, Decimal)) for arg in args)


def is_integer_numeric(*args: Any) -> bool:
    """
    Check if the arguments are of integer numeric types.
    """
    from pylogic.constant import Constant

    return all(
        isinstance(arg, int)
        or (isinstance(arg, Constant) and isinstance(arg.value, int))
        for arg in args
    )


def is_iterable(obj: Any) -> bool:
    """
    Check if the object is iterable.
    """
    try:
        iter(obj)
        return True
    except TypeError:
        return False


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


def has_been_proven(to_prove: Proposition, proven: Proposition) -> bool:
    """
    Check if `to_prove` is equal to `proven`, and `proven` is proven.
    """
    return to_prove == proven and proven.is_proven


@overload
def todo(arg: P) -> P: ...
@overload
def todo(arg: P, *args: *Ps) -> tuple[P, *Ps]: ...
def todo(arg: P, *args: *Ps) -> P | tuple[P, *Ps]:
    all_args = (arg, *args)
    for argmnt in all_args:
        argmnt.todo()  # type: ignore
    if len(all_args) == 1:
        return arg
    return all_args


@overload
def python_to_pylogic(arg: P) -> P: ...
@overload
def python_to_pylogic(arg: E) -> E: ...
@overload
def python_to_pylogic(arg: S) -> S: ...
@overload
def python_to_pylogic(arg: TSet) -> TSet: ...
@overload
def python_to_pylogic(arg: TSequence) -> TSequence: ...
@overload
def python_to_pylogic(arg: tuple | list) -> Sequence: ...
@overload
def python_to_pylogic(arg: set | dict) -> Set: ...
@overload
def python_to_pylogic(arg: dict) -> Set: ...
@overload
def python_to_pylogic(arg: TNumeric) -> Constant[TNumeric]: ...
@overload
def python_to_pylogic(arg: str) -> Constant[str] | Sequence: ...
@overload
def python_to_pylogic(arg: Any) -> Proposition | Expr | Symbol | Sequence | Set: ...
def python_to_pylogic(arg: Any) -> Proposition | Expr | Symbol | Sequence | Set:
    """
    Convert certain python objects to Pylogic objects.
    A Python character/str with one character is converted to a Pylogic Constant.
    A Python set is converted to a Pylogic Set.
    A Python dictionary is converted to a Pylogic Set of Pairs.
    A Python tuple is converted to a Pylogic Pair, Triple, or Sequence.
    A Python int, float, Fraction, complex, or Decimal is converted to a Pylogic Constant.
    A Python iterable (str included) besides those above is converted to a Pylogic Sequence.

    Raises TypeError if arg is not one of the above.
    """
    from pylogic.constant import Constant
    from pylogic.proposition.proposition import Proposition
    from pylogic.structures.sequence import Pair, Sequence, Triple
    from pylogic.structures.set_ import Set
    from pylogic.symbol import Symbol

    # TODO: add more types or use base class
    if isinstance(arg, (Symbol, Proposition, Expr, Set, Sequence)):
        return arg

    if isinstance(arg, (str, bytes)):
        if len(arg) == 1:
            return Constant(arg[0])
        else:
            return Sequence(
                name=str(arg), initial_terms=[python_to_pylogic(i) for i in arg]
            )

    if isinstance(arg, set):
        return Set(name=str(arg), elements={python_to_pylogic(i) for i in arg})
    if isinstance(arg, dict):
        pair_str = lambda k, v: str((k, v))
        return Set(
            name=str(arg),
            elements={Pair(pair_str(k, v), k, v) for k, v in arg.items()},
        )
    if isinstance(arg, tuple):
        if len(arg) == 2:
            return Pair(str(arg), *arg)
        if len(arg) == 3:
            return Triple(str(arg), *arg)
        else:
            return Sequence(
                name=str(arg), initial_terms=[python_to_pylogic(i) for i in arg]
            )

    if isinstance(arg, (int, float, Fraction, complex, Decimal)):
        return Constant(arg)
    if is_iterable(arg):
        return Sequence(
            name=str(arg), initial_terms=[python_to_pylogic(i) for i in arg]
        )
    else:
        raise TypeError(f"Cannot convert {arg} to a Pylogic object.")


def latex(arg: Any) -> str:
    from pylogic.expressions.expr import Expr
    from pylogic.proposition.proposition import Proposition
    from pylogic.structures.sequence import Sequence
    from pylogic.structures.set_ import Set
    from pylogic.symbol import Symbol

    if isinstance(arg, (Expr, Symbol, Set, Proposition, Sequence)):
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


class Getter(Generic[T]):
    """
    Get the actual key object reference in a dict/set when its value
    is equal to some other object.
    from https://stackoverflow.com/a/78219110/22426744
    """

    __slots__ = "key", "value"

    def __init__(self, key, value: T | None = None):
        self.key = key  # other object we use to find this reference
        self.value: T | None = value  # actual reference

    def __repr__(self):
        return "{}({}, {})".format(
            type(self).__name__,
            repr(self.key),
            repr(self.value),
        )

    def __hash__(self):
        return hash(self.key)

    def __eq__(self, other: T):
        # when __contains__ is called for most of these types eg set, dict,
        # it calles the __eq__ method of this key object
        # eg set.__contains__(getter) -> getter.__eq__(element)
        self.value: T = other
        return self.key == other


RAISES = object()


def getkey(keyed: Container, key: T, default=RAISES) -> T:
    getter = Getter[T](key)
    if getter in keyed:
        # providing '__contains__' is implemented to call
        #  the '__eq__' method (which in any sane case it
        #  should be), this results in our special
        #  'Getter.__eq__' method being called with the
        #  element we're trying to get as the 'other' argument
        return getter.value
    if default is RAISES:
        raise KeyError(key)
    return default  # type: ignore


@overload
def ternary_not(val: bool) -> bool: ...
@overload
def ternary_not(val: None) -> None: ...
def ternary_not(val: bool | None) -> bool | None:
    return not val if val is not None else None


@overload
def ternary_or(*vals: bool) -> bool: ...
@overload
def ternary_or(*vals: None) -> None: ...
@overload
def ternary_or(*vals: bool | None) -> bool | None: ...
def ternary_or(*val1: bool | None) -> bool | None:
    none_count = 0
    for val in val1:
        if val is True:
            return True
        none_count += val is None
    if none_count > 0:
        return None
    return False


@overload
def ternary_and(*vals: bool) -> bool: ...
@overload
def ternary_and(*vals: None) -> None: ...
@overload
def ternary_and(*vals: bool | None) -> bool | None: ...
def ternary_and(*vals: bool | None) -> bool | None:
    none_count = 0
    for val in vals:
        if val is False:
            return False
        none_count += val is None
    if none_count > 0:
        return None
    return True


def ternary_if_not_none(val: bool | None, default: bool | None) -> bool | None:
    return val if val is not None else default


def is_prime(num: int | Fraction | Constant[int] | Constant[Fraction]) -> bool:
    from pylogic.constant import Constant

    if isinstance(num, Constant):
        num = num.value
    if isinstance(num, Fraction):
        if num.denominator == 1:
            num = int(num.numerator)
        else:
            return False
    if not isinstance(num, int):
        return False

    if num <= 1:
        return False
    if num == 2:
        return True
    if num % 2 == 0:
        return False

    i = 3
    while i < num**0.5 + 1:
        if num % i == 0:
            return False
        i += 2
    return True


def Rational(
    numerator: Term | PythonNumeric, denominator: Term | PythonNumeric
) -> Constant[Fraction]:
    from pylogic.constant import Constant

    if isinstance(numerator, int) and isinstance(denominator, int):
        return Constant(Fraction(numerator, denominator))
    num, denom = python_to_pylogic(numerator), python_to_pylogic(denominator)
    return num / denom


class Namespace(SimpleNamespace):
    """
    Attributes can be accessed using dot notation or dictionary subscript notation.
    """

    def __init__(self, dict_: dict[str, Any] | None = None, **kwargs: Any):
        dict_ = dict_ or {}
        dict_.update(kwargs)
        for key, value in dict_.items():
            if isinstance(value, dict):
                setattr(self, key, Namespace(value))
            else:
                setattr(self, key, value)

    def __setattr__(self, name: str, value: Any) -> None:
        return super().__setattr__(name, value)

    def __delattr__(self, name: str) -> None:
        raise TypeError("Cannot delete attributes from a Namespace")

    def __getitem__(self, key: str) -> Any:
        return getattr(self, key)

    def __str__(self) -> str:
        return str(vars(self))


def _make_assumption(
    term: Symbol | Sequence | Set | SequenceTerm, attr: str, value: bool
) -> Proposition:
    """
    Create the assumption proposition that the assumption attribute represents.
    """
    # TODO: needs to be tested properly, somewhat hacky but
    # the most straightforward way to add assumptions on Symbols/Sequence
    # due to cyclic dependencies

    import importlib

    from pylogic.proposition.not_ import Not
    from pylogic.proposition.relation.contains import IsContainedIn
    from pylogic.proposition.relation.subsets import IsSubsetOf
    from pylogic.structures.set_ import SeqSet

    set_modules = {
        "real": "pylogic.theories.real_numbers",
        "rational": "pylogic.theories.rational_numbers",
        "integer": "pylogic.theories.integers",
        "natural": "pylogic.theories.natural_numbers",
        "finite": "pylogic.structures.set_",
    }
    set_names = {
        "real": "Reals",
        "rational": "Rationals",
        "integer": "Integers",
        "natural": "Naturals",
        "finite": "AllFiniteSequences",
    }

    positive_prop = None
    if attr in set_modules:
        mod = importlib.import_module(set_modules[attr])
        mod_set = getattr(mod, set_names[attr])
        if term.is_sequence and attr != "finite":
            positive_prop = IsSubsetOf(SeqSet(term), mod_set)
        elif term.is_set and attr != "finite":
            positive_prop = IsSubsetOf(term, mod_set)
        else:
            positive_prop = IsContainedIn(term, mod_set)
    elif attr == "zero":
        from pylogic.proposition.relation.equals import Equals

        positive_prop = Equals(term, 0)
    elif attr == "nonpositive":
        from pylogic.proposition.ordering.lessorequal import LessOrEqual

        positive_prop = LessOrEqual(term, 0)
    elif attr == "nonnegative":
        from pylogic.proposition.ordering.greaterorequal import GreaterOrEqual

        positive_prop = GreaterOrEqual(term, 0)
    elif attr == "positive":
        from pylogic.proposition.ordering.greaterthan import GreaterThan

        positive_prop = GreaterThan(term, 0)
    elif attr == "negative":
        from pylogic.proposition.ordering.lessthan import LessThan

        positive_prop = LessThan(term, 0)
    elif attr == "even":
        if term.is_natural:
            from pylogic.theories.natural_numbers import Naturals

            positive_prop = Naturals.even(term)
        elif term.is_integer:
            from pylogic.theories.integers import Integers

            positive_prop = Integers.even(term)

    elif attr == "odd":
        if term.is_natural:
            from pylogic.theories.natural_numbers import Naturals

            positive_prop = Naturals.odd(term)
        elif term.is_integer:
            from pylogic.theories.integers import Integers

            positive_prop = Integers.odd(term)

    elif attr == "finite" and term.is_sequence:
        from pylogic.proposition.relation.contains import IsContainedIn
        from pylogic.structures.set_ import AllFiniteSequences

        positive_prop = IsContainedIn(term, AllFiniteSequences)
    elif attr == "finite" and term.is_set:
        from pylogic.proposition.relation.contains import IsContainedIn
        from pylogic.structures.set_ import AllFiniteSets

        positive_prop = IsContainedIn(term, AllFiniteSets)
    if positive_prop is None:
        raise ValueError(f"Unknown assumption: {attr} on {term}")
    if value:
        prop = positive_prop
    else:
        prop = Not(positive_prop)
    return prop


def _add_assumption_props(
    term: Symbol | Sequence | Set, kwargs: dict[str, Any]
) -> None:
    """
    Add assumption propositions to the term based on the assumptions.
    """
    from pylogic.variable import Variable

    context = kwargs.get("context", None)

    explicit_assumptions_attrs = {
        "real",
        "rational",
        "integer",
        "natural",
        "zero",
        "nonpositive",
        "nonnegative",
        "positive",
        "negative",
        "even",
        "odd",
        "finite",
        "sequence",
        "set_",
    } & kwargs.keys()
    # if "positive" in explicit_assumptions_attrs:
    #     explicit_assumptions_attrs.add("nonnegative")
    #     explicit_assumptions_attrs.add("zero")
    # if "negative" in explicit_assumptions_attrs:
    #     explicit_assumptions_attrs.add("nonpositive")
    #     explicit_assumptions_attrs.add("zero")

    new_kwargs = kwargs.copy()

    term_is_real = kwargs.get(
        "real",
        kwargs.get("rational", kwargs.get("integer", kwargs.get("natural", None))),
    )
    if kwargs.get("nonpositive", None) is False and term_is_real:
        new_kwargs["positive"] = True
    if kwargs.get("nonnegative", None) is False and term_is_real:
        new_kwargs["negative"] = True
    if kwargs.get("even", None) is False and kwargs.get(
        "integer", kwargs.get("natural", None)
    ):
        new_kwargs["odd"] = True

    # for sequences & sets
    if term.is_sequence or term.is_set:
        term.properties_of_each_term = []

    _add_assumption_attributes(term, new_kwargs)

    # TODO: needs to be tested properly, somewhat hacky but
    # the most straightforward way to add assumptions on Symbols
    # due to cyclic dependencies
    # this needs to be done after the all above attributes are set (dependencies, etc)
    # this order is important; add the set assumptions first before the others
    for attr in [
        "finite",
        "real",
        "rational",
        "integer",
        "natural",
        "zero",
        "nonpositive",
        "nonnegative",
        "positive",
        "negative",
        "even",
        "odd",
    ]:
        if getattr(term, f"_is_{attr}") is None:
            continue

        # adding assumptions to SequenceTerm or set element
        # so no need finite
        if term.is_sequence and attr != "finite":
            from pylogic.proposition.quantified.forall import ForallInSet
            from pylogic.theories.natural_numbers import Naturals
            from pylogic.variable import Variable

            n = Variable("n")
            term_n = term[n]  # type: ignore defined for Variable and Sequence
            prop1 = _make_assumption(term_n, attr, getattr(term, f"_is_{attr}"))  # type: ignore
            prop1 = ForallInSet(n, Naturals, prop1)
        elif term.is_set and attr != "finite":
            from pylogic.proposition.quantified.forall import ForallInSet
            from pylogic.variable import Variable

            x = Variable("x")
            prop1 = _make_assumption(x, attr, getattr(term, f"_is_{attr}"))
            prop1 = ForallInSet(x, term, prop1)  # type: ignore

        if (term.is_sequence or term.is_set) and attr != "finite":
            # in any of the above cases, we add the assumption
            prop1._set_is_assumption(
                True,
                add_to_context=attr in explicit_assumptions_attrs,
                context=context,
            )
            term.properties_of_each_term.append(prop1)
            term.knowledge_base.add(prop1)

        if (term.is_sequence or term.is_set) and attr not in {
            "real",
            "rational",
            "integer",
            "natural",
            "finite",
        }:
            continue

        # we also add props for the sequence/set itself
        # these are subset relations, or
        # containment relation for "finite"
        prop = _make_assumption(term, attr, getattr(term, f"_is_{attr}"))

        # hack: for sequence/set, I don't want to add the subset relation as well
        # to the context because ForallInSet above
        # is already added
        # unless for "finite" where it was not added
        if (term.is_sequence or term.is_set) and attr != "finite":
            prop.is_assumption = True
        else:
            prop._set_is_assumption(
                True,
                add_to_context=attr in explicit_assumptions_attrs,
                context=context,
            )
        term.knowledge_base.add(prop)


def _add_assumption_attributes(term: Symbol | Set | Sequence, kwargs) -> None:
    """
    Add attributes to the term based on the assumptions.
    Check for contradictions and raise ValueError if found.
    To be used with Symbol and Sequence.
    """
    # # no need to set natural when nonnegative and integer are True
    # # because the getter handles that
    # if kwargs.get("natural", None):
    #     term.is_nonnegative = True
    #     term.is_integer = True

    if kwargs.get("positive", None):
        term.is_real = True
        term.is_nonnegative = True
        if term._is_nonpositive is None:
            term.is_nonpositive = False
        elif term._is_nonpositive is True:
            raise ValueError(
                "Contradictory assumptions: A positive number cannot be nonpositive"
            )
        if term._is_zero is None:
            term.is_zero = False
        elif term._is_zero is True:
            raise ValueError(
                "Contradictory assumptions: A positive number cannot be zero"
            )
    if kwargs.get("positive", None) is False:
        if term._is_real and term._is_nonpositive is None:
            term.is_nonpositive = True
        elif term._is_real and term._is_nonpositive is False:
            raise ValueError(
                "Contradictory assumptions: A positive number cannot be nonpositive"
            )
        if term._is_real and term._is_nonpositive is None:
            term.is_nonpositive = True
        elif term._is_real and term._is_nonpositive is False:
            raise ValueError(
                "Contradictory assumptions: A number must be positive or nonpositive"
            )

    if kwargs.get("negative", None):
        term.is_real = True
        term.is_nonpositive = True
        if term._is_nonnegative is None:
            term._is_nonnegative = False
        elif term._is_nonnegative is True:
            raise ValueError(
                "Contradictory assumptions: A negative number cannot be nonnegative"
            )
        if term._is_zero is None:
            term.is_zero = False
        elif term._is_zero is True:
            raise ValueError(
                "Contradictory assumptions: A negative number cannot be zero"
            )
    if kwargs.get("negative", None) is False:
        if term._is_real and term._is_nonnegative is None:
            term.is_nonnegative = True
        elif term._is_real and term._is_nonnegative is False:
            raise ValueError(
                "Contradictory assumptions: A number must be negative or nonnegative"
            )
        if term._is_real and term._is_nonnegative is None:
            term.is_nonnegative = True
        elif term._is_real and term._is_nonnegative is False:
            raise ValueError(
                "Contradictory assumptions: A number must be negative or nonnegative"
            )
    if kwargs.get("odd", None):
        if term._is_integer and term._is_odd is None:
            term.is_odd = True
            term.is_even = False
        elif term._is_integer and term._is_odd is False:
            raise ValueError("Contradictory assumptions: An odd number cannot be even")
    if kwargs.get("even", None):
        if term._is_integer and term._is_even is None:
            term.is_even = True
            term.is_odd = False
        elif term._is_integer and term._is_even is False:
            raise ValueError(
                "Contradictory assumptions: An integer must be odd or even"
            )

    if term._is_zero or term._is_nonpositive or term._is_nonnegative:
        if term._is_real is None:
            term.is_real = True
        elif term._is_real is False:
            raise ValueError(
                "Contradictory assumptions: A number cannot be both non-real and zero/nonpositive/nonnegative"
            )
    if term._is_zero:
        if term._is_even is None:
            term.is_even = True
        elif term._is_even is False:
            raise ValueError(
                "Contradictory assumptions: A number cannot be both zero and odd"
            )
        if (term._is_nonnegative is False) or term._is_nonpositive is False:
            raise ValueError(
                "Contradictory assumptions: A number cannot be both zero and negative/positive"
            )
        else:
            if term._is_nonnegative is None:
                term.is_nonnegative = True
            if term._is_nonpositive is None:
                term.is_nonpositive = True
    if term._is_nonnegative and term._is_nonpositive:
        if term._is_zero is None:
            term.is_zero = True
        elif term._is_zero is False:
            raise ValueError(
                "Contradictory assumptions: A number cannot be nonnegative, nonpositive and nonzero"
            )
    if term._is_even or term._is_odd:
        if term._is_integer is None:
            term.is_integer = True
            if term._is_nonnegative:
                term.is_natural = True
        elif term._is_integer is False:
            raise ValueError(
                "Contradictory assumptions: A number cannot be both non-integer and even"
            )
