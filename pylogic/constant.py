from __future__ import annotations

from fractions import Fraction
from typing import Any, Generic, Self, TypeVar, cast

from pylogic.helpers import is_numeric, type_check
from pylogic.symbol import Symbol

T = TypeVar("T", str, int, float, complex, Fraction)


class Constant(Symbol, Generic[T]):
    def __init__(self, value: T, *args, **kwargs) -> None:
        type_check(
            value, str, int, float, complex, Fraction, context="Constant.__init__"
        )

        self.value: T = cast(T, value)

        # if the constant is created from a proven existential statement
        # it qwon't be equal to any other constant
        self._from_existential_instance = kwargs.get(
            "_from_existential_instance", False
        )
        super().__init__(str(value), *args, **kwargs)

    def __eq__(self, other: Any) -> bool:
        """
        Constant(0) == 0
        """
        if isinstance(other, Constant):
            return (not self._from_existential_instance) and self.value == other.value
        return self.value == other

    def __hash__(self) -> int:
        return super().__hash__()

    def copy(self) -> Self:
        return self
