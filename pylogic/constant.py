from __future__ import annotations

from decimal import Decimal
from fractions import Fraction
from typing import TYPE_CHECKING, Any, Generic, Self, TypeVar, cast, overload

from pylogic.enviroment_settings.settings import settings
from pylogic.helpers import is_python_numeric, type_check
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
    def __init__(self, value: T, *args, **kwargs) -> None:
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
        self.value: T = cast(T, value)
        super().__init__(str(value), *args, **kwargs)
        # if the constant is created from a proven existential statement
        # it won't be equal to any other constant
        self._from_existential_instance = kwargs.get(
            "_from_existential_instance", False
        )
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
        elif isinstance(value, (Decimal, float)):
            self._is_real = True

    def __eq__(self, other: Any) -> bool:
        """
        Constant(0) == 0
        """
        from pylogic.proposition.proposition import Proposition
        from pylogic.structures.sequence import Sequence
        from pylogic.structures.set_ import Set
        from pylogic.variable import Variable

        if self is other:
            return True
        if isinstance(other, Constant):
            return (
                (not self._from_existential_instance)
                and (not other._from_existential_instance)
                and self.value == other.value
            )
        if isinstance(other, (Variable, Set, Sequence, Proposition)):
            return False
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
    def to_sympy(self: Constant[str]) -> PylSympySymbol: ...
    def to_sympy(
        self,
    ) -> PylSympySymbol | sp.Integer | sp.Float | sp.Add | sp.Rational | ImaginaryUnit:
        if is_python_numeric(self.value):
            import sympy as sp

            return sp.sympify(self.value)
        return super().to_sympy()

    def deepcopy(self) -> Self:
        return self

    def copy(self) -> Self:
        return self


def Rational(numerator: int, denominator: int) -> Constant[Fraction]:
    return Constant(Fraction(numerator, denominator))


oo = Infinity = Constant(float("inf"))
