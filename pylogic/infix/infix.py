from __future__ import annotations

from functools import partial
from typing import Any, Callable, Generic, TypeVar

T = TypeVar("T")
U = TypeVar("U")
V = TypeVar("V")
W = TypeVar("W")


class InfixOnly(Generic[T, U, V]):
    def __init__(self, operate: Callable[[T, U], V], symbol: str | None = None):
        self.operate: Callable[[T, U], V] = operate
        self.symbol: str | None = symbol

    def __eq__(self, value: object) -> bool:
        if not isinstance(value, InfixOnly):
            return False
        return self.operate is value.operate

    def __ror__(self, other: T) -> PrefixOnly[U, V]:
        return PrefixOnly(partial(self.operate, other))


class PrefixOnly(InfixOnly, Generic[T, V]):
    operate: Callable[[T], V]

    def __init__(self, operate: Callable[[T], V], symbol: str | None = None):
        super().__init__(operate, symbol)  # type: ignore

    def __or__(self, other: T) -> V:
        return self.operate(other)


class Infix(InfixOnly, Generic[T, U, V]):
    def __init__(self, operate: Callable[[T, U], V], symbol: str | None = None):
        super().__init__(operate, symbol)

    def __ror__(self, other: T) -> Prefix[U, V]:
        return Prefix(partial(self.operate, other))

    def __call__(self, v1: T, v2: U) -> V:
        return self.operate(v1, v2)


class Prefix(PrefixOnly, Generic[T, V]):
    def __init__(self, operate: Callable[[T], V], symbol: str | None = None):
        super().__init__(operate, symbol)

    def __or__(self, other: T) -> V:
        return super().__or__(other)

    def __call__(self, v1: T) -> V:
        return self.operate(v1)


class SpecialInfix(InfixOnly, Generic[T, U, V, W]):
    """
    A special infix operator that can be called.
    T is the left operand type.
    U is the right operand type.
    V is the return type when used as an infix operator.
    W is the return type when called.
    """

    operate: Callable[[T, U], V]

    def __init__(
        self,
        operate: Callable[[T, U], V],
        call: Callable[..., W] | None = None,
        symbol: str | None = None,
    ):
        super().__init__(operate, symbol)
        self.call: Callable[..., W] | None = call

    def __ror__(self, other: T) -> PrefixOnly[U, V]:
        return super().__ror__(other)

    def __call__(self, *args: Any, **kwds: Any) -> W:
        if self.call is None:
            raise NotImplementedError
        return self.call(*args, **kwds)

    def __eq__(self, value: object) -> bool:
        if not isinstance(value, SpecialInfix):
            return False
        return self.operate is value.operate and self.call is value.call
