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


l: list[int] = []

l2: MutableOnlyList[even] = l

m = list[even]()
n = list[Cls[int, str]]()


reveal_type([5].sort)

f(l)
f2(l)
f3(l)
g(m, m)
reveal_type(l)

h(n, l)


f4: Callable[[int | str], TypeIs[int]] = lambda _: cast(TypeIs[int], _ > 0)  # type: ignore


def w() -> Callable[[int | str], TypeIs[int]] | None: ...
def w2() -> int | str: ...


f5: Callable[[int | str], TypeIs[int]] | None = w()

g2 = f5 or f4

x: int | str = w2()

if g2(x):
    reveal_type(x)


U = TypeVar("U")


class NoIncludeType[T]:

    # def __init__(self, arg: T) -> None:
    #     if hasattr(self, "__orig_class__"):
    #         # check the type passed to the generic class
    #         if not isinstance(arg, self.__orig_class__.__args__[0]):  # type: ignore
    #             raise TypeError(f"Expected type {self.__orig_class__.__args__[0]}, got {type(arg)}")  # type: ignore
    #     else:
    #         raise TypeError("NoIncludeType must have the type argument specified")  # type: ignore
    #     self.arg = arg
    @overload
    def __call__(self, arg: T) -> Never: ...
    @overload
    def __call__(self, arg: U) -> U: ...
    def __call__(self, arg: T | U) -> U:
        if hasattr(self, "__orig_class__"):
            # check the type passed to the generic class
            if not isinstance(arg, self.__orig_class__.__args__[0]):  # type: ignore
                raise TypeError(f"Expected type {self.__orig_class__.__args__[0]}, got {type(arg)}")  # type: ignore
        return arg  # type: ignore


A = TypeVar("A", covariant=True)
B = TypeVar("B", covariant=True)


@overload
def no_include_type(arg: A, type_: Callable[[Any], TypeIs[A]]) -> Never: ...
@overload
def no_include_type(arg: B, type_: Callable[[Any], TypeIs[A]]) -> B: ...
def no_include_type(arg: A | B, type_: Callable[[Any], TypeIs[A]]) -> B: ...


class s1(str):
    pass


def no_process_str(arg: Any) -> int:
    z: str = ""
    w: int = 0
    y = NoIncludeType[str]()(z)
    return 0


def no_process_str2(arg: Any) -> int:
    z: str = ""
    is_str: Callable[[Any], TypeIs[str]] = lambda x: isinstance(x, str)  # type: ignore
    w: int = 0
    y = no_include_type(w, is_str)
