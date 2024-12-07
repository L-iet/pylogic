from __future__ import annotations

from decimal import Decimal
from fractions import Fraction
from typing import TYPE_CHECKING, Any, Generic, Self, TypeVar, cast, overload

from pylogic.enviroment_settings.settings import settings
from pylogic.helpers import (
    is_prime,
    is_python_numeric,
    is_python_real_numeric,
    type_check,
)
from pylogic.symbol import Symbol

if TYPE_CHECKING:
    import sympy as sp
    from sympy.core.numbers import ImaginaryUnit

    from pylogic.proposition.not_ import Not
    from pylogic.proposition.ordering.greaterorequal import GreaterOrEqual
    from pylogic.proposition.ordering.greaterthan import GreaterThan
    from pylogic.proposition.ordering.lessorequal import LessOrEqual
    from pylogic.proposition.ordering.lessthan import LessThan
    from pylogic.proposition.relation.equals import Equals
    from pylogic.sympy_helpers import PylSympySymbol

T = TypeVar("T", bound=str | int | float | complex | Fraction | Decimal)


class Constant(Symbol, Generic[T]):
    def __new__(cls, value: T, *args, **kwargs) -> Constant[T]:
        if kwargs.get("set_", kwargs.get("set", False)):
            from pylogic.structures.set_ import Set

            return Set(value, *args, **kwargs)
        if kwargs.get("sequence", False):
            from pylogic.structures.sequence import Sequence

            return Sequence(value, *args, **kwargs)
        return object.__new__(cls)

    def __init__(self, value: T, *args, **kwargs) -> None:

        # although value can be numeric, it gets routed back
        # to Constant.__new_init__
        # better to use kwarg value=value here so that
        # value is part of kwargs in Symbol.__init__ and Symbol.__copy_init__
        super().__init__(*args, value=value, **kwargs)  # type: ignore

        self.kwargs = self.kwargs + [("value", "value")]

    def __new_init__(self, value: T, *args, **kwargs) -> None:
        type_check(
            value,
            str,
            int,
            float,
            complex,
            Fraction,
            Decimal,
            context="Constant.__init__",
        )
        if isinstance(value, Constant):
            value = value.value
        # __init__ depends on value: __init__ -> add to set -> hash -> __eq__ -> .value
        self.value: T = cast(T, value)
        super().__new_init__(str(value), *args, **kwargs)
        # if the constant is created from a proven existential statement
        # it won't be equal to any other constant
        self._from_existential_instance = kwargs.get(
            "_from_existential_instance", False
        )
        # since this is the __init__, we technically don't
        # need to use the main setter methods
        if isinstance(value, int):
            self._is_integer = True
            if value >= 0:
                self._is_natural = True
            else:
                self._is_natural = False
        elif isinstance(value, Fraction):
            self._is_rational = True
            if value.denominator == 1:
                self._is_integer = True
                if value >= 0:
                    self._is_natural = True
                else:
                    self._is_natural = False
            else:
                self._is_integer = False
        elif isinstance(value, (Decimal, float)) and value not in [
            float("inf"),
            float("-inf"),
        ]:
            self.is_real = True

        if is_python_real_numeric(value):
            if value >= 0:
                self._is_nonnegative = True
            else:
                self._is_nonnegative = False
            if value <= 0:
                self._is_nonpositive = True
            else:
                self._is_nonpositive = False
            if value == 0:
                self._is_zero = True
            else:
                self._is_zero = False
            if value % 2 == 0:
                self._is_even = True
            else:
                self._is_even = False

        # Warning: this will raise an error if a Constant prime number is created
        # in an initializer that runs in the call stack to create Naturals
        if is_prime(value):
            from pylogic.inference import Inference
            from pylogic.theories.natural_numbers import Naturals

            self.knowledge_base.add(
                Naturals.prime(
                    self,
                    _is_proven=True,
                    _assumptions=set(),
                    _inference=Inference(None, rule="by_definition"),
                )
            )

    def __eq__(self, other: Any) -> bool:
        """
        Constant(0) == 0
        """
        from pylogic.helpers import is_python_numeric
        from pylogic.proposition.proposition import Proposition
        from pylogic.structures.sequence import Sequence
        from pylogic.structures.set_ import Set
        from pylogic.variable import Variable

        if self is other:
            return True
        if isinstance(other, Constant):
            return self.value == other.value
        if isinstance(other, (Variable, Set, Sequence, Proposition)):
            return False
        if is_python_numeric(other):
            return self.value == other
        return NotImplemented

    def __lt__(self, other: Any) -> bool | LessThan:
        from pylogic.proposition.ordering.lessthan import LessThan

        if settings["PYTHON_OPS_RETURN_PROPS"]:
            return LessThan(self, other)
        if isinstance(other, Constant):
            return self.value < other.value
        return self.value < other

    def __le__(self, other: Any) -> bool | LessOrEqual:
        from pylogic.proposition.ordering.lessorequal import LessOrEqual

        if settings["PYTHON_OPS_RETURN_PROPS"]:
            return LessOrEqual(self, other)
        if isinstance(other, Constant):
            return self.value <= other.value
        return self.value <= other

    def __gt__(self, other: Any) -> bool | GreaterThan:
        from pylogic.proposition.ordering.greaterthan import GreaterThan

        if settings["PYTHON_OPS_RETURN_PROPS"]:
            return GreaterThan(self, other)
        if isinstance(other, Constant):
            return self.value > other.value
        return self.value > other

    def __ge__(self, other: Any) -> bool | GreaterOrEqual:
        from pylogic.proposition.ordering.greaterorequal import GreaterOrEqual

        if settings["PYTHON_OPS_RETURN_PROPS"]:
            return GreaterOrEqual(self, other)
        if isinstance(other, Constant):
            return self.value >= other.value
        return self.value >= other

    def __hash__(self) -> int:
        return super().__hash__()

    def __int__(self) -> int:
        return int(self.value)

    def __float__(self) -> float:
        return float(self.value)

    def __complex__(self) -> complex:
        return complex(self.value)

    def to_fraction(self) -> Fraction:
        if isinstance(self.value, Fraction):
            return self.value
        raise TypeError(f"{self.value} is not a Fraction")

    def to_decimal(self) -> Decimal:
        if isinstance(self.value, Decimal):
            return self.value
        raise TypeError(f"{self.value} is not a Decimal")

    @overload
    def to_sympy(self: Constant[int]) -> sp.Integer: ...
    @overload
    def to_sympy(self: Constant[float]) -> sp.Float: ...
    @overload
    def to_sympy(self: Constant[complex]) -> sp.Add: ...
    @overload
    def to_sympy(self: Constant[Fraction]) -> sp.Rational: ...
    @overload
    def to_sympy(self: Constant[Decimal]) -> sp.Float: ...
    @overload
    def to_sympy(self: Constant[str]) -> sp.Symbol: ...
    def to_sympy(
        self,
    ) -> sp.Symbol | sp.Integer | sp.Float | sp.Add | sp.Rational | ImaginaryUnit:
        if is_python_numeric(self.value):
            import sympy as sp

            return sp.sympify(self.value)
        return super().to_sympy()

    def deepcopy(self) -> Self:
        return self

    def copy(self) -> Self:
        return self


@overload
def constants(value: T, **kwargs) -> Constant[T]: ...
@overload
def constants(*args: T, **kwargs) -> tuple[Constant[T], ...]: ...
def constants(
    *args: T,
    **kwargs: T,
) -> Constant | tuple[Constant[T], ...]:
    """
    Create multiple Constant instances at once.
    """
    if len(args) == 1:
        return Constant(args[0], **kwargs)
    return tuple(Constant(value, **kwargs) for value in args)


oo = Infinity = Constant(float("inf"))
