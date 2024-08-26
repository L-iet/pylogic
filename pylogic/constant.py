from __future__ import annotations
from typing import Generic, TypeVar, Any, cast
from fractions import Fraction
from pylogic.symbol import Symbol
from pylogic.helpers import type_check

T = TypeVar("T", str, int, float, complex, Fraction)

_constant_values = set()


class Constant(Symbol, Generic[T]):
    def __init__(self, value: T, *args, **kwargs) -> None:
        type_check(
            value, str, int, float, complex, Fraction, context="Constant.__init__"
        )

        global _constant_values
        existing = value in _constant_values
        if existing:
            raise ValueError(f"Constant {value} already exists")
        _constant_values.add(value)

        self.value: T = cast(T, value)
        super().__init__(str(value), *args, **kwargs)

    def __eq__(self, other: Any) -> bool:
        if isinstance(other, Constant):
            return self.value == other.value
        return self.value == other

    def __hash__(self) -> int:
        return super().__hash__()
