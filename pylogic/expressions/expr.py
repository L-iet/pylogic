from __future__ import annotations
from typing import TYPE_CHECKING, Self, Any, TypeVar, overload, Literal
from abc import ABC, abstractmethod
from fractions import Fraction
from pylogic.structures.sets import Set

import sympy as sp

if TYPE_CHECKING:
    from pylogic.symbol import Symbol

    Numeric = Fraction | int | float
    PBasic = Symbol | Numeric


class Expr(ABC):
    is_real = None

    def __init__(self, *args: PBasic | Expr):
        self.args = args

    @abstractmethod
    def evaluate(self) -> sp.Basic:
        pass

    @abstractmethod
    def _latex(self) -> str:
        pass

    @abstractmethod
    def __str__(self) -> str:
        pass

    def _repr_latex_(self) -> str:
        return f"$${self._latex()}$$"

    def __repr__(self) -> str:
        return f"{self.__class__.__name__}({', '.join(map(repr, self.args))})"

    def __copy__(self) -> Self:
        return self.copy()

    def __add__(self, other: Expr | PBasic) -> Add:
        return Add(self, other)

    def __sub__(self, other: Expr | PBasic) -> Add:
        return Add(self, -other)  # type: ignore

    def __mul__(self, other: Expr | PBasic) -> Mul:
        return Mul(self, other)

    def __truediv__(self, other: Expr | PBasic) -> Mul:
        return Mul(self, Pow(other, -1))

    def __neg__(self) -> Mul:
        return Mul(-1, self)

    def __pow__(self, other: Expr | PBasic) -> Pow:
        return Pow(self, other)

    def __radd__(self, other: Expr | PBasic) -> Add:
        return Add(other, self)

    def __rsub__(self, other: Expr | PBasic) -> Add:
        return Add(other, -self)

    def __rmul__(self, other: Expr | PBasic) -> Mul:
        return Mul(other, self)

    def __rtruediv__(self, other: Expr | PBasic) -> Mul:
        return Mul(other, Pow(self, -1))

    def __rpow__(self, other: Expr | PBasic) -> Pow:
        return Pow(other, self)

    def equals(self, other: Any) -> bool:
        """
        Check if two expressions are equal, essentially identical.
        """
        if isinstance(other, Expr):
            return self.args == other.args
        return False

    def __eq__(self, other: Any) -> bool:
        """
        Check if two expressions evaluate to the same value.
        """
        if isinstance(other, Expr):
            return self.evaluate() == other.evaluate()
        return self.evaluate() == other

    def __hash__(self) -> int:
        return hash((self.__class__.__name__, self.args))

    def replace(self, old: Any, new: Any) -> Self:
        new_args = [replace(arg, old, new) for arg in self.args]
        return self.__class__(*new_args)

    def copy(self) -> Self:
        return self.__class__(*self.args)

    def doit(self) -> sp.Basic:
        return self.evaluate().doit()


if TYPE_CHECKING:
    T = TypeVar("T", bound=Expr | PBasic, covariant=True)


class Add(Expr):
    def __init__(self, *args: Expr | PBasic):
        super().__init__(*args)
        for arg in args:
            if isinstance(arg, (int, float, Fraction)) or arg.is_real:
                continue
            else:
                self.is_real = None
                break
        else:
            self.is_real = True

    def evaluate(self) -> sp.Add:
        return sp.Add(*[evaluate(arg) for arg in self.args])

    def _latex(self) -> str:
        return "{" + " + ".join([_latex(a) for a in self.args]) + "}"

    def __str__(self) -> str:
        return " + ".join(map(str, self.args))


class Mul(Expr):
    def __init__(self, *args: PBasic | Expr):
        super().__init__(*args)
        for arg in args:
            if isinstance(arg, (int, float, Fraction)) or arg.is_real:
                continue
            else:
                self.is_real = None
                break
        else:
            self.is_real = True

    def evaluate(self) -> sp.Mul:
        return sp.Mul(*[evaluate(arg) for arg in self.args])

    def _latex(self) -> str:
        args = []
        for arg in self.args:
            if isinstance(arg, Add):
                args.append(rf"\left({_latex(arg)}\right)")
            else:
                args.append(str(arg))
        return "{" + r" \cdot ".join(args) + "}"

    def __str__(self) -> str:
        args = []
        for arg in self.args:
            if isinstance(arg, Add):
                args.append(f"({arg})")
            else:
                args.append(str(arg))
        return f"{' * '.join(args)}"


class Pow(Expr):
    def __init__(self, base: PBasic | Expr, exp: PBasic | Expr):
        self.base = base
        self.exp = exp
        self.is_real = None
        super().__init__(base, exp)

    def evaluate(self) -> sp.Pow:
        return sp.Pow(evaluate(self.base), evaluate(self.exp))

    def _latex(self) -> str:
        if (
            isinstance(self.base, Symbol)
            or isinstance(self.base, int)
            or isinstance(self.base, float)
        ):
            base_latex = _latex(self.base)
        else:
            base_latex = rf"\left({_latex(self.base)}\right)"
        exp_latex = _latex(self.exp)
        return "{" + f"{base_latex}^{{{exp_latex}}}" + "}"

    def __str__(self) -> str:
        from pylogic.symbol import Symbol

        if (
            isinstance(self.base, Symbol)
            or isinstance(self.base, int)
            or isinstance(self.base, float)
        ):
            base_str = str(self.base)
        else:
            base_str = f"({self.base})"
        if isinstance(self.exp, int) or isinstance(self.exp, float):
            power_str = str(self.exp)
        else:
            power_str = f"({self.exp})"
        return f"{base_str}^{power_str}"


def replace(
    expr: PBasic | Expr,
    old: Any,
    new: Any,
) -> PBasic | Expr:
    if expr == old:
        return new
    elif isinstance(expr, Expr):
        return expr.replace(old, new)
    else:
        return expr


def evaluate(expr: sp.Basic | PBasic | Expr | Set) -> sp.Basic:
    from pylogic.symbol import Symbol

    if isinstance(expr, int):
        return sp.Integer(expr)
    if isinstance(expr, float):
        return sp.Float(expr)
    if isinstance(expr, Fraction):
        return sp.Rational(expr)
    if isinstance(expr, (Expr, Symbol, Set)):
        return expr.evaluate()
    return expr


@overload
def maybe_evaluate(
    expr: sp.Basic, should_evaluate: Literal[False] = False
) -> sp.Basic: ...


@overload
def maybe_evaluate(expr: T, should_evaluate: Literal[False] = False) -> T: ...


@overload
def maybe_evaluate(
    expr: sp.Basic | T, should_evaluate: bool = False
) -> sp.Basic | T: ...


def maybe_evaluate(expr: sp.Basic | T, should_evaluate: bool = False) -> sp.Basic | T:
    if should_evaluate:
        return evaluate(expr)
    return expr


@overload
def sqrt(expr: PBasic | Expr, evaluate: Literal[False] = False) -> Pow: ...
@overload
def sqrt(expr: PBasic | Expr, evaluate: Literal[True] = True) -> sp.Basic: ...
def sqrt(expr: PBasic | Expr, evaluate=False) -> sp.Basic | Pow:
    return maybe_evaluate(Pow(expr, Fraction(1, 2)), evaluate)


@overload
def mul(*args: PBasic | Expr, evaluate: Literal[False] = False) -> Mul: ...
@overload
def mul(*args: PBasic | Expr, evaluate: Literal[True] = True) -> sp.Basic: ...
def mul(*args: PBasic | Expr, evaluate=False) -> sp.Basic | Mul:
    return maybe_evaluate(Mul(*args), evaluate)


@overload
def add(*args: PBasic | Expr, evaluate: Literal[False] = False) -> Add: ...
@overload
def add(*args: PBasic | Expr, evaluate: Literal[True] = True) -> sp.Basic: ...
def add(*args: PBasic | Expr, evaluate=False) -> sp.Basic | Add:
    return maybe_evaluate(Add(*args), evaluate)


@overload
def sub(
    a: PBasic | Expr, b: PBasic | Expr, evaluate: Literal[False] = False
) -> Add: ...
@overload
def sub(
    a: PBasic | Expr, b: PBasic | Expr, evaluate: Literal[True] = True
) -> sp.Basic: ...
def sub(a: PBasic | Expr, b: PBasic | Expr, evaluate=False) -> sp.Basic | Add:
    return maybe_evaluate(Add(a, -b), evaluate)


@overload
def div(
    a: PBasic | Expr, b: PBasic | Expr, evaluate: Literal[False] = False
) -> Mul: ...
@overload
def div(
    a: PBasic | Expr, b: PBasic | Expr, evaluate: Literal[True] = True
) -> sp.Basic: ...
def div(a: PBasic | Expr, b: PBasic | Expr, evaluate=False) -> sp.Basic | Mul:
    return maybe_evaluate(Mul(a, Pow(b, -1)), evaluate)


def _latex(expr: PBasic | Expr) -> str:
    if isinstance(expr, Expr):
        return expr._latex()
    return "{" + str(expr) + "}"
