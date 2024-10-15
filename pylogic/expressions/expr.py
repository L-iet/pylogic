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

from pylogic import PBasic, Term, Unification

if TYPE_CHECKING:
    from pylogic.proposition.proposition import Proposition
    from pylogic.proposition.relation.contains import IsContainedIn
    from pylogic.proposition.relation.equals import Equals
    from pylogic.structures.class_ import Class
    from pylogic.structures.sequence import Sequence
    from pylogic.structures.set_ import Set
    from pylogic.symbol import Symbol
    from pylogic.sympy_helpers import PylSympySymbol
    from pylogic.variable import Variable
else:
    Symbol = Any
    Variable = Any


class Expr(ABC):
    def __init__(
        self, *args: Proposition | PBasic | Set | Sequence | Expr, **kwargs: Any
    ):
        from pylogic.helpers import python_to_pylogic

        assert len(args) > 0, "Must provide at least one argument"
        args = tuple(map(python_to_pylogic, args))
        self._build_args_and_symbols(*args)
        self._init_args = args
        self._init_kwargs = kwargs
        self.knowledge_base: set[Proposition] = set()
        self.is_real: bool | None = None
        self.is_rational: bool | None = None
        self.is_integer: bool | None = None
        self.is_natural: bool | None = None

    def _build_args_and_symbols(
        self, *args: Proposition | PBasic | Set | Sequence | Expr
    ) -> None:
        from pylogic.constant import Constant
        from pylogic.structures.set_ import Set
        from pylogic.variable import Variable

        self.args = args
        self.variables: set[Variable] = set()  # variables present in this expression
        self.independent_dependencies: set[Variable] = set()
        self.constants: set[Constant] = set()
        self.sets: set[Set] = set()  # sets present in this expression
        self.class_ns: set[Class] = set()

        # TODO: arg can be a proposition, a sequence as well
        for arg in args:
            if isinstance(arg, Variable):
                self.variables.add(arg)
                if len(arg.depends_on) == 0:
                    self.independent_dependencies.add(arg)
            elif isinstance(arg, Constant):
                self.constants.add(arg)
            elif isinstance(arg, Set):
                self.sets.add(arg)
            elif isinstance(arg, Expr):
                self.symbols.update(arg.symbols)
                self.sets.update(arg.sets)
                self.variables.update(arg.variables)
                self.constants.update(arg.constants)
                self.class_ns.update(arg.class_ns)
                self.independent_dependencies.update(arg.independent_dependencies)
            else:
                cls = arg.__class__.__name__
                if cls.startswith("Collection") and cls[10].isdigit():
                    self.class_ns.add(arg)  # type: ignore

    @property
    def symbols(self) -> set[Symbol]:
        return self.variables.union(self.constants)  # type: ignore

    @property
    def atoms(self) -> set[Class | Set | Symbol]:
        # TODO: add function
        return self.symbols.union(self.sets).union(self.class_ns)

    @abstractmethod
    def evaluate(self) -> Expr:
        pass

    @abstractmethod
    def to_sympy(self) -> sp.Basic:
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
        return NotImplemented

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

    def is_in(self, other: Set | Variable, **kwargs) -> IsContainedIn:
        from pylogic.proposition.relation.contains import IsContainedIn

        return IsContainedIn(self, other, **kwargs)

    def __hash__(self) -> int:
        return hash((self.__class__.__name__, self.args))

    def replace(self, replace_dict: dict, equal_check: Callable | None = None) -> Self:
        """
        For replacing subexpressions in an expression.
        `equal_check` is a function that checks if two
        objects are equal in order to replace.
        """
        for old in replace_dict:
            new = replace_dict[old]
            if equal_check is None:
                if old == self:
                    return new
            else:
                if equal_check(old, self):
                    return new
        new_args = [
            replace(arg, replace_dict, equal_check=equal_check)
            for arg in self._init_args
        ]
        new_kwargs = {
            k: replace(v, replace_dict, equal_check=equal_check)
            for k, v in self._init_kwargs.items()
        }
        new_expr = self.__class__(*new_args, **new_kwargs)
        return new_expr

    def copy(self) -> Self:
        return self.__class__(*self._init_args, **self._init_kwargs)

    def deepcopy(self) -> Self:
        return self.copy()

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


U = TypeVar("U", bound=Term)


class CustomExpr(Expr, Generic[U]):
    """
    U is the return type after evaluating the expression,
    unless it is not fully evaluated.
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
        return NotImplemented

    def to_sympy(self) -> sp.Expr:
        return sp.Expr(*[to_sympy(arg) for arg in self.args])

    def evaluate(self) -> Self | U:
        """
        Calls the evaluation function with the arguments.
        """
        if self.eval_func is None:
            return self
        evaluated = self.eval_func(*self.args)
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

    def _latex(self) -> str:
        from pylogic.helpers import latex

        return rf"\left({latex(self.left)} {self.symbol} {latex(self.right)}\right)"

    def __str__(self) -> str:
        return f"({self.left} {self.symbol} {self.right})"


class Add(Expr):
    def __init__(self, *args: Expr | PBasic):
        super().__init__(*args)
        self.is_real = object()  # type: ignore
        self.is_rational = object()  # type: ignore
        self.is_integer = object()  # type: ignore
        self.is_natural = object()  # type: ignore
        for arg in self._init_args:
            if (
                self.is_real is not None and not arg.is_real
            ):  # arg.is_real is False or None
                self.is_real = None
            if self.is_rational is not None and not arg.is_rational:
                self.is_rational = None
            if self.is_integer is not None and not arg.is_integer:
                self.is_integer = None
            if self.is_natural is not None and not arg.is_natural:
                self.is_natural = None
        if self.is_real is not None:
            self.is_real = True
        if self.is_rational is not None:
            self.is_rational = True
        if self.is_integer is not None:
            self.is_integer = True
        if self.is_natural is not None:
            self.is_natural = True

    def evaluate(self) -> Add:
        from pylogic.sympy_helpers import sympy_to_pylogic

        return sympy_to_pylogic(self.to_sympy())

    def to_sympy(self) -> sp.Add:
        return sp.Add(*[to_sympy(arg) for arg in self.args])

    def _latex(self) -> str:
        from pylogic.helpers import latex

        return r"{\left(" + " + ".join([latex(a) for a in self.args]) + r"\right)}"

    def __str__(self) -> str:
        return " + ".join(map(str, self.args))


class Mul(Expr):
    def __init__(self, *args: PBasic | Expr):
        super().__init__(*args)
        self.is_real = object()  # type: ignore
        self.is_rational = object()  # type: ignore
        self.is_integer = object()  # type: ignore
        self.is_natural = object()  # type: ignore
        for arg in self._init_args:
            if (
                self.is_real is not None and not arg.is_real
            ):  # arg.is_real is False or None
                self.is_real = None
            if self.is_rational is not None and not arg.is_rational:
                self.is_rational = None
            if self.is_integer is not None and not arg.is_integer:
                self.is_integer = None
            if self.is_natural is not None and not arg.is_natural:
                self.is_natural = None
        if self.is_real is not None:
            self.is_real = True
        if self.is_rational is not None:
            self.is_rational = True
        if self.is_integer is not None:
            self.is_integer = True
        if self.is_natural is not None:
            self.is_natural = True

    def evaluate(self) -> Mul:
        from pylogic.sympy_helpers import sympy_to_pylogic

        return sympy_to_pylogic(self.to_sympy())

    def to_sympy(self) -> sp.Mul:
        return sp.Mul(*[to_sympy(arg) for arg in self.args])

    def _latex(self) -> str:
        from pylogic.helpers import latex

        args = []
        for arg in self.args:
            if isinstance(arg, Add):
                args.append(rf"\left({latex(arg)}\right)")
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
        self.is_rational = None
        self.is_integer = None
        self.is_natural = None
        super().__init__(base, exp)
        base, exp = self._init_args
        if base.is_real:
            if exp.is_integer:
                self.is_real = True
        if base.is_rational:
            if exp.is_integer:
                self.is_rational = True
        if base.is_integer:
            if exp.is_integer:
                self.is_rational = True
            if exp.is_natural:
                self.is_integer = True
        if base.is_natural:
            if exp.is_integer:
                self.is_rational = True
            if exp.is_natural:
                self.is_natural = True
            if exp.is_rational:
                self.is_real = True

    def evaluate(self) -> Pow:
        from pylogic.sympy_helpers import sympy_to_pylogic

        return sympy_to_pylogic(self.to_sympy())

    def to_sympy(self) -> sp.Pow:
        return sp.Pow(to_sympy(self.base), to_sympy(self.exp))

    def _latex(self) -> str:
        from pylogic.helpers import latex

        if (
            isinstance(self.base, Symbol)
            or isinstance(self.base, int)
            or isinstance(self.base, float)
        ):
            base_latex = latex(self.base)
        else:
            base_latex = rf"\left({latex(self.base)}\right)"
        exp_latex = latex(self.exp)
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
    expr: Any,
    replace_dict: dict,
    equal_check: Callable | None = None,
) -> Any:
    """
    For replacing subexpressions in an expression.
    `equal_check` is a function that checks if two
    objects are equal in order to replace.
    """
    from pylogic.proposition.proposition import Proposition
    from pylogic.symbol import Symbol

    equal_check = equal_check or (lambda x, y: x == y)

    for old in replace_dict:
        new = replace_dict[old]
        if equal_check(old, expr):
            return new

    if isinstance(expr, (list, set, tuple)):
        return type(expr)(
            replace(e, replace_dict, equal_check=equal_check) for e in expr
        )

    # TODO: update with more types
    if not isinstance(expr, (Expr, Proposition, Symbol)):
        return expr

    if isinstance(expr, (Expr, Proposition)):
        return expr.replace(replace_dict, equal_check=equal_check)
    return expr


@overload
def to_sympy(expr: int) -> sp.Integer: ...
@overload
def to_sympy(expr: float) -> sp.Float: ...
@overload
def to_sympy(expr: Fraction) -> sp.Rational: ...
@overload
def to_sympy(expr: Expr) -> sp.Basic: ...
@overload
def to_sympy(expr: Symbol) -> PylSympySymbol: ...
@overload
def to_sympy(expr: Set) -> sp.Set: ...
def to_sympy(expr: PBasic | Expr | Set) -> sp.Basic:
    from pylogic.structures.set_ import Set
    from pylogic.symbol import Symbol

    # TODO: add sequence and other types

    if isinstance(expr, int):
        return sp.Integer(expr)
    if isinstance(expr, float):
        return sp.Float(expr)
    if isinstance(expr, Fraction):
        return sp.Rational(expr)
    if isinstance(expr, (Expr, Symbol, Set)):
        return expr.to_sympy()
    return expr


def sqrt(expr: PBasic | Expr) -> Pow:
    return Pow(expr, Fraction(1, 2))


def mul(*args: PBasic | Expr) -> Mul:
    return Mul(*args)


def add(*args: PBasic | Expr) -> Add:
    return Add(*args)


def sub(a: PBasic | Expr, b: PBasic | Expr) -> Add:
    return Add(a, -b)


def div(a: PBasic | Expr, b: PBasic | Expr) -> Mul:
    return Mul(a, Pow(b, -1))
