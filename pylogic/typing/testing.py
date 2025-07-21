from __future__ import annotations
from typing import (
    Any,
    Callable,
    Protocol,
    TypeIs,
    TypeVar,
    cast,
    Never,
    TYPE_CHECKING,
    overload,
)
from pylogic.typing.collection import MutableOnlyList, ReadOnlyList


class even(int):
    pass


class mul4(even):
    pass


class odd(int):
    pass


def f(x: MutableOnlyList[even]) -> None:
    x.append(even())
    x.append(mul4())


def f2(x: MutableOnlyList[odd]) -> None:
    x.append(odd())


def f3(x: MutableOnlyList[int]) -> None:
    x.append(odd())
    x.append(even())


class Cls[A, B]: ...


def g[A, B](x: ReadOnlyList[A], y: list[B]) -> A: ...


def h[A, B, C](x: ReadOnlyList[Cls[A, B]], y: list[C]) -> tuple[A, B, C]: ...


def g2(x: MutableOnlyList[list[int]]) -> None: ...


def g3(x: ReadOnlyList[MutableOnlyList[int]]) -> None: ...


l: list[int] = []

l2: MutableOnlyList[even] = l

m = list[even]()
n = list[Cls[int, str]]()
l3: list[list[int]] = [[]]


reveal_type([5].sort)

f(l)
f2(l)
f3(l)
g(m, m)
g2(l3)
g3(l3)
reveal_type(l)

h(n, l)


f4: Callable[[int | str], TypeIs[int]] = lambda _: cast(TypeIs[int], _ > 0)  # type: ignore


def w() -> Callable[[int | str], TypeIs[int]] | None: ...
def w2() -> int | str: ...


f5: Callable[[int | str], TypeIs[int]] | None = w()

g3 = f5 or f4

x: int | str = w2()

if g3(x):
    reveal_type(x)


U = TypeVar("U")
