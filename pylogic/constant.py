from __future__ import annotations
from typing import Generic, TypeVar, Any
from fractions import Fraction
from pylogic.symbol import Symbol

T = TypeVar("T", str, int, float, complex, Fraction)


class Constant(Symbol, Generic[T]):
    def __init__(self, value: T, *args, **kwargs) -> None:
        self.value: T = value
        super().__init__(str(value), *args, **kwargs)

    def __eq__(self, other: Any) -> bool:
        if isinstance(other, Constant):
            return self.value == other.value
        return self.value == other

    def __hash__(self) -> int:
        return super().__hash__()


Const = Constant(5)
