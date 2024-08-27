from __future__ import annotations

from abc import ABC, abstractmethod
from fractions import Fraction
from typing import (
    TYPE_CHECKING,
    Any,
    Callable,
    Generic,
    Literal,
    Self,
    TypeVar,
    overload,
)

import sympy as sp

from pylogic.structures.set_ import Set

if TYPE_CHECKING:
    from pylogic.proposition.relation.contains import IsContainedIn
    from pylogic.proposition.relation.equals import Equals
    from pylogic.symbol import Symbol
    from pylogic.variable import Variable

    Numeric = Fraction | int | float
    PBasic = Symbol | Numeric


class Expr(ABC):
    is_real = None

    def __init__(self, *args: PBasic | Expr, **kwargs: Any):
        assert len(args) > 0, "Must provide at least one argument"
        self._build_args_and_symbols(*args)
        self._init_args = args
        self._init_kwargs = kwargs

    def _build_args_and_symbols(self, *args: PBasic | Expr) -> None:
        from pylogic.symbol import Symbol

        self.args = args
        self.symbols: set[Symbol] = set()  # symbols present in this expression
        for arg in args:
            if isinstance(arg, Symbol):
                self.symbols.add(arg)
            elif isinstance(arg, Expr):
                self.symbols.update(arg.symbols)

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

    def __eq__(self, other: Any) -> bool:
        """
        Check if two expressions are structurally equal, essentially identical.
        """
        if isinstance(other, Expr):
            return isinstance(other, self.__class__) and self.args == other.args
        return False

    def eval_same(self, other: Any) -> bool:
        """
        Check if two expressions evaluate to the same value.
        """
        if self == other:
            return True
        if isinstance(other, Expr):
            return self.evaluate() == other.evaluate()
        return self.evaluate() == other

    def equals(self, other: Term, **kwargs) -> Equals:
        from pylogic.proposition.relation.equals import Equals

        return Equals(self, other, **kwargs)

    def is_in(self, other: Set, **kwargs) -> IsContainedIn:
        from pylogic.proposition.relation.contains import IsContainedIn

        return IsContainedIn(self, other, **kwargs)

    def __hash__(self) -> int:
        return hash((self.__class__.__name__, self.args))

    def replace(self, old: Any, new: Any) -> Self:
        new_args = [replace(arg, old, new) for arg in self.args]
        new_expr = self.copy()
        new_expr._build_args_and_symbols(*new_args)
        return new_expr

    def copy(self) -> Self:
        return self.__class__(*self._init_args, **self._init_kwargs)

    def doit(self) -> sp.Basic:
        return self.evaluate().doit()

    def unify(self, other: Self) -> Unification | Literal[True] | None:
        """
        Algorithm to unify two expressions.
        If unification succeeds, a dictionary of values to instantiate variables
        to is returned.
        The dictionary never instantiates a variable `y` to variable `y`.
        It may instantiate a variable `y` to variable `x` or a variable
        `y` to a symbol or value `y`.
        If no instantiations need to be made (eg propositions are equal),
        return True.
        Otherwise (unification fails), return None.
        """
        if self.__class__ != other.__class__ or len(self.args) != len(other.args):
            return None
        from pylogic.helpers import unify as term_unify

        d: Unification = {}
        for s_arg, o_arg in zip(self.args, other.args):
            res = term_unify(s_arg, o_arg)
            if isinstance(res, dict):
                for k in res:
                    if k in d and d[k] != res[k]:
                        return None
                    d[k] = res[k]
            elif res is None:
                return None
        if len(d) == 0:
            return True
        else:
            return d


if TYPE_CHECKING:
    T = TypeVar("T", bound=Expr | PBasic, covariant=True)
    Unevaluated = Symbol | Set | Expr
    Term = Unevaluated | Numeric | sp.Basic
    Unification = dict[Variable, Term]

U = TypeVar("U")


class CustomExpr(Expr, Generic[U]):
    """
    U is the return type after evaluating the expression.
    """

    def __init__(
        self,
        name: str,
        *args: PBasic | Expr,
        eval_func: Callable[..., U] | None = None,
        latex_func: Callable[..., str] | None = None,
    ):
        super().__init__(*args)
        self.name = name
        self.eval_func = eval_func
        self.latex_func = latex_func
        self._init_args = (name, *args)
        self._init_kwargs = {"eval_func": eval_func, "latex_func": latex_func}

    def __repr__(self) -> str:
        return f"CustomExpr{self.name.capitalize()}({', '.join(map(repr, self.args))})"

    def __hash__(self) -> int:
        return hash((self.__class__.__name__, self.name, self.args))

    def __eq__(self, other: Any) -> bool:
        if isinstance(other, CustomExpr):
            return (
                self.name == other.name
                and self.eval_func is other.eval_func
                and self.args == other.args
            )
        return False

    def evaluate(self) -> U:
        """
        Calls the evaluation function with the arguments.
        May not return a sympy object, depending on eval_func.
        """
        from pylogic.symbol import Symbol

        if self.eval_func is None:
            raise NotImplementedError(f"Cannot evaluate {self.name}")
        evaluated = self.eval_func(*self.args)
        if isinstance(evaluated, (Expr, Symbol)):
            return evaluated.evaluate()
        return evaluated

    def _latex(self) -> str:
        if self.latex_func is None:
            return repr(self)
        return self.latex_func(*self.args)

    def __str__(self) -> str:
        return f"{self.name}({', '.join(map(str, self.args))})"


class BinaryExpression(CustomExpr[U]):
    def __init__(
        self,
        name: str,
        symbol: str,
        left: PBasic | Expr,
        right: PBasic | Expr,
        eval_func: Callable[[U, U], U] | None = None,
        latex_func: Callable[[str, str], str] | None = None,
    ):
        super().__init__(name, left, right, eval_func=eval_func, latex_func=latex_func)
        self.symbol = symbol
        self.left = left
        self.right = right
        self._init_args = (name, symbol, left, right)

    def __repr__(self) -> str:
        return f"BinOp{self.name.capitalize()}({self.left}, {self.right})"

    def replace(self, old: Any, new: Any) -> Self:
        new_left = replace(self.left, old, new)
        new_right = replace(self.right, old, new)
        new_expr = self.copy()
        new_expr._build_args_and_symbols(new_left, new_right)
        new_expr.left = new_left
        new_expr.right = new_right
        return new_expr

    def _latex(self) -> str:
        return f"{_latex(self.left)} {self.symbol} {_latex(self.right)}"

    def __str__(self) -> str:
        return f"({self.left} {self.symbol} {self.right})"


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

    def replace(self, old: Any, new: Any) -> Self:
        new_base = replace(self.base, old, new)
        new_exp = replace(self.exp, old, new)
        new_expr = self.copy()
        new_expr._build_args_and_symbols(new_base, new_exp)
        new_expr.base = new_base
        new_expr.exp = new_exp
        return new_expr

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
