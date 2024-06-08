from __future__ import annotations
from typing import TYPE_CHECKING, Self, Any, TypeVar
from abc import ABC, abstractmethod
from fractions import Fraction
import sympy as sp


if TYPE_CHECKING:
    from pylogic.symbol import Symbol

    Basic = Symbol | int | float | Fraction


class Expr(ABC):
    is_real = None

    def __init__(self, *args: Basic | Expr):
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

    def __add__(self, other: Expr | Basic) -> Add:
        return Add(self, other)

    def __sub__(self, other: Expr | Basic) -> Add:
        return Add(self, -other)  # type: ignore

    def __mul__(self, other: Expr | Basic) -> Mul:
        return Mul(self, other)

    def __truediv__(self, other: Expr | Basic) -> Mul:
        return Mul(self, Pow(other, -1))

    def __neg__(self) -> Mul:
        return Mul(-1, self)

    def __pow__(self, other: Expr | Basic) -> Pow:
        return Pow(self, other)

    def __radd__(self, other: Expr | Basic) -> Add:
        return Add(other, self)

    def __rsub__(self, other: Expr | Basic) -> Add:
        return Add(other, -self)

    def __rmul__(self, other: Expr | Basic) -> Mul:
        return Mul(other, self)

    def __rtruediv__(self, other: Expr | Basic) -> Mul:
        return Mul(other, Pow(self, -1))

    def __rpow__(self, other: Expr | Basic) -> Pow:
        return Pow(other, self)

    def __eq__(self, other: Any) -> bool:
        if isinstance(other, Expr):
            return self.args == other.args
        return False

    def __hash__(self) -> int:
        return hash((self.__class__.__name__, self.args))

    def replace(self, old: Any, new: Any) -> Self:
        new_args = [replace(arg, old, new) for arg in self.args]
        return self.__class__(*new_args)

    def copy(self) -> Self:
        return self.__class__(*self.args)

    def doit(self) -> Any:
        return self.evaluate().doit()


class Add(Expr):
    def __init__(self, *args: Expr | Basic):
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
    def __init__(self, *args: Basic | Expr):
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
    def __init__(self, base: Basic | Expr, exp: Basic | Expr):
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


T = TypeVar("T", bound=Expr | Basic)


def replace(
    expr: Basic | Expr,
    old: Any,
    new: Any,
) -> Basic | Expr:
    if expr == old:
        return new
    elif isinstance(expr, Expr):
        return expr.replace(old, new)
    else:
        return expr


def evaluate(expr: sp.Basic | Basic | Expr) -> sp.Basic:
    from pylogic.symbol import Symbol

    if isinstance(expr, int):
        return sp.Integer(expr)
    if isinstance(expr, float):
        return sp.Float(expr)
    if isinstance(expr, Fraction):
        return sp.Rational(expr)
    if isinstance(expr, (Expr, Symbol)):
        return expr.evaluate()
    return expr


def maybe_evaluate(expr: T, should_evaluate=False) -> sp.Basic | T:
    if should_evaluate:
        return evaluate(expr)
    return expr


def sqrt(expr: Basic | Expr, evaluate=False) -> sp.Basic | Pow:
    return maybe_evaluate(Pow(expr, Fraction(1, 2)), evaluate)


def mul(*args: Basic | Expr, evaluate=False) -> sp.Basic | Mul:
    return maybe_evaluate(Mul(*args), evaluate)


def add(*args: Basic | Expr, evaluate=False) -> sp.Basic | Add:
    return maybe_evaluate(Add(*args), evaluate)


def sub(a: Basic | Expr, b: Basic | Expr, evaluate=False) -> sp.Basic | Add:
    return maybe_evaluate(Add(a, -b), evaluate)


def div(a: Basic | Expr, b: Basic | Expr, evaluate=False) -> sp.Basic | Mul:
    return maybe_evaluate(Mul(a, Pow(b, -1)), evaluate)


def _latex(expr: Basic | Expr) -> str:
    if isinstance(expr, Expr):
        return expr._latex()
    return "{" + str(expr) + "}"
