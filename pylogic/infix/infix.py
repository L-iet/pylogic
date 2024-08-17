from __future__ import annotations
from typing import Callable, Any, Generic, TypeVar
from functools import partial

T = TypeVar("T")
U = TypeVar("U")
V = TypeVar("V")
W = TypeVar("W")


class InfixOnly(Generic[T, U, V]):
    def __init__(self, operate: Callable[[T, U], V]):
        self.operate: Callable[[T, U], V] = operate

    def __ror__(self, other: T) -> PrefixOnly[U, V]:
        return PrefixOnly(partial(self.operate, other))


class PrefixOnly(InfixOnly, Generic[T, V]):
    operate: Callable[[T], V]

    def __init__(self, operate: Callable[[T], V]):
        super().__init__(operate)  # type: ignore

    def __or__(self, other: T) -> V:
        return self.operate(other)


class Infix(InfixOnly, Generic[T, U, V]):
    def __init__(self, operate: Callable[[T, U], V]):
        super().__init__(operate)

    def __ror__(self, other: T) -> Prefix[U, V]:
        return Prefix(partial(self.operate, other))

    def __call__(self, v1: T, v2: U) -> V:
        return self.operate(v1, v2)


class Prefix(PrefixOnly, Generic[T, V]):
    def __init__(self, operate: Callable[[T], V]):
        super().__init__(operate)

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

    def __init__(self, operate: Callable[[T, U], V]):
        super().__init__(operate)

    def __ror__(self, other: T) -> PrefixOnly[U, V]:
        return super().__ror__(other)

    def __call__(self, *args: Any, **kwds: Any) -> W:
        return self.call(*args, **kwds)

    def call(self, *args: Any, **kwds: Any) -> W:
        raise NotImplementedError
