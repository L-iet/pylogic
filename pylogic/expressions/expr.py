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
from pylogic.enviroment_settings.settings import settings

if TYPE_CHECKING:
    from pylogic.expressions.abs import Abs
    from pylogic.proposition.not_ import Not
    from pylogic.proposition.ordering.greaterorequal import GreaterOrEqual
    from pylogic.proposition.ordering.greaterthan import GreaterThan
    from pylogic.proposition.ordering.lessorequal import LessOrEqual
    from pylogic.proposition.ordering.lessthan import LessThan
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
    is_atomic = False
    _is_wrapped = False

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
        self.is_zero: bool | None = None
        self.is_nonpositive: bool | None = None
        self.is_nonnegative: bool | None = None
        self.is_even: bool | None = None

    @property
    def is_positive(self) -> bool | None:
        from pylogic.helpers import ternary_and, ternary_not

        return ternary_and(ternary_not(self.is_zero), self.is_nonnegative)

    @property
    def is_negative(self) -> bool | None:
        from pylogic.helpers import ternary_and, ternary_not, ternary_or

        return ternary_and(ternary_not(self.is_zero), self.is_nonpositive)

    @property
    def is_odd(self) -> bool | None:
        from pylogic.helpers import ternary_not

        return ternary_not(self.is_even)

    @property
    def is_nonzero(self) -> bool | None:
        from pylogic.helpers import ternary_not

        return ternary_not(self.is_zero)

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

        self.sets_contained_in: set[Set] = set()

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

    def __abs__(self) -> Abs:
        from pylogic.expressions.abs import Abs

        return Abs(self)

    def __pow__(self, other: Expr | PBasic) -> Pow:
        return Pow(self, other)

    def __radd__(self, other: Expr | PBasic) -> Add:
        return Add(other, self)

    def __rsub__(self, other: Expr | PBasic) -> Add:
        return Add(other, -self)

    def __rmul__(self, other: Expr | PBasic) -> Mul:
        return Mul(other, self)

    def __rtruediv__(self, other: Expr | PBasic) -> Mul | Pow:
        if other == 1:
            return Pow(self, -1)
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

    def __lt__(self, other: Any) -> bool | LessThan:
        from pylogic.proposition.ordering.lessthan import LessThan

        if settings["PYTHON_OPS_RETURN_PROPS"]:
            return LessThan(self, other)
        return NotImplemented

    def __le__(self, other: Any) -> bool | LessOrEqual:
        from pylogic.proposition.ordering.lessorequal import LessOrEqual

        if settings["PYTHON_OPS_RETURN_PROPS"]:
            return LessOrEqual(self, other)
        return NotImplemented

    def __gt__(self, other: Any) -> bool | GreaterThan:
        from pylogic.proposition.ordering.greaterthan import GreaterThan

        if settings["PYTHON_OPS_RETURN_PROPS"]:
            return GreaterThan(self, other)
        return NotImplemented

    def __ge__(self, other: Any) -> bool | GreaterOrEqual:
        from pylogic.proposition.ordering.greaterorequal import GreaterOrEqual

        if settings["PYTHON_OPS_RETURN_PROPS"]:
            return GreaterOrEqual(self, other)
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

    def _is_in_by_rule(
        self, other: Set | Class | Variable, rule: str = "by_definition"
    ) -> IsContainedIn:
        from pylogic.inference import Inference
        from pylogic.proposition.relation.contains import IsContainedIn

        res = IsContainedIn(
            self,
            other,
            _is_proven=True,
            _assumptions=set(),
            _inference=Inference(None, rule=rule),
        )
        return res

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
        eval_func: Callable[..., U | None] | None = None,
        latex_func: Callable[..., str] | None = None,
    ):
        super().__init__(*args)
        self.name = name
        self.eval_func = eval_func
        self.latex_func = latex_func
        self._init_args = (name, *args)
        self._init_kwargs = {"eval_func": eval_func, "latex_func": latex_func}

        # if the latex repr is wrapped (eg in a function call)
        # so that we can avoid parentheses
        self._is_wrapped = latex_func is None

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
        if evaluated is None:
            return self
        return evaluated

    def _latex(self) -> str:
        if self.latex_func is None:
            return rf"\text{{{repr(self)}}}"
        return self.latex_func(*self.args)

    def __str__(self) -> str:
        return f"{self.name}({', '.join(map(str, self.args))})"

    def __repr__(self) -> str:
        return f"CustomExpr_{self.name}({', '.join(map(repr, self.args))})"


def distance(
    a, b, eval_func: Callable[[U, U], Term | None] | None = None
) -> CustomExpr:
    """
    General distance function.

    Returns an expression representing the 'distance' between two terms.

    When evaluated, it returns the absolute value of the difference for real numbers,
    or the result of the evaluation function for other types.
    """
    return CustomExpr(
        "distance",
        a,
        b,
        eval_func=lambda x, y: (
            abs(x - y)
            if x.is_real and y.is_real
            else (eval_func(x, y) if eval_func else None)
        ),
    )


class BinaryExpression(CustomExpr[U]):
    def __init__(
        self,
        name: str,
        symbol: str,
        left: PBasic | Expr,
        right: PBasic | Expr,
        eval_func: Callable[[U, U], U | None] | None = None,
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
        return rf"\left({self.left._latex()} {self.symbol} {self.right._latex()}\right)"

    def __str__(self) -> str:
        return f"({self.left} {self.symbol} {self.right})"


class Add(Expr):
    # order of operations for expressions (0-indexed)
    # Function MinElement Abs SequenceTerm Pow Prod Mul Sum Add Binary_Expr
    # Custom_Expr Piecewise Relation(eg <, subset)
    _precedence = 8

    def __init__(self, *args: Expr | PBasic):
        from pylogic.helpers import ternary_or

        super().__init__(*args)
        all_real = True
        all_rational = True
        all_integer = True
        all_natural = True
        all_nonnegative = True
        all_zero = True
        all_nonpositive = True
        all_even = True
        exists_positive = False
        exists_negative = False
        count_odd = 0
        count_even = 0
        total_args = len(self._init_args)
        for i, arg in enumerate(self._init_args):
            if not arg.is_real:
                all_real = False
            if not arg.is_rational:
                all_rational = False
            if not arg.is_integer:
                all_integer = False
            if not arg.is_natural:
                all_natural = False
            if not arg.is_nonnegative:
                all_nonnegative = False
            if not arg.is_zero:
                all_zero = False
            if not arg.is_nonpositive:
                all_nonpositive = False
            if arg.is_even:
                count_even += 1
            elif not arg.is_even:
                all_even = False
            if arg.is_even is False:
                count_odd += 1
            if arg.is_positive:
                exists_positive = True
            if arg.is_negative:
                exists_negative = True
        self.is_real = ternary_or(all_real, None)
        self.is_rational = ternary_or(all_rational, None)
        self.is_integer = ternary_or(all_integer, None)
        self.is_natural = ternary_or(all_natural, None)
        self.is_nonnegative = ternary_or(all_nonnegative, None)
        self.is_zero = ternary_or(all_zero, None)
        self.is_nonpositive = ternary_or(all_nonpositive, None)
        self.is_even = ternary_or(all_even, None)

        if all_nonnegative and exists_positive:
            self.is_zero = False
        if all_nonpositive and exists_negative:
            self.is_zero = False
        if count_odd % 2 == 0 and count_even == total_args - count_odd:
            self.is_even = True
        elif count_odd % 2 == 1 and count_even == total_args - count_odd:
            self.is_even = False

    def evaluate(self) -> Add:
        from pylogic.sympy_helpers import sympy_to_pylogic

        return sympy_to_pylogic(self.to_sympy())

    def to_sympy(self) -> sp.Add:
        return sp.Add(*[to_sympy(arg) for arg in self.args])

    def _latex(self) -> str:
        wrap = lambda p: (
            rf"\left({p._latex()}\right)"
            if not p.is_atomic
            and not p._is_wrapped
            and p.__class__._precedence >= self.__class__._precedence
            else p._latex()
        )
        return " + ".join(map(wrap, self.args))

    def __str__(self) -> str:
        wrap = lambda p: (
            f"({p})"
            if not p.is_atomic
            and not p._is_wrapped
            and p.__class__._precedence >= self.__class__._precedence
            else str(p)
        )
        return " + ".join(map(wrap, self.args))


class Mul(Expr):
    # order of operations for expressions (0-indexed)
    # Function MinElement Abs SequenceTerm Pow Prod Mul Sum Add Binary_Expr
    # Custom_Expr Piecewise Relation(eg <, subset)
    _precedence = 6

    def __init__(self, *args: PBasic | Expr):
        from pylogic.helpers import ternary_or

        super().__init__(*args)
        all_real = True
        all_rational = True
        all_integer = True
        all_natural = True
        all_nonzero = True
        count_nonpositive = 0
        count_nonnegative = 0
        exists_zero = False
        count_even = 0
        count_odd = 0
        total_args = len(self._init_args)

        for i, arg in enumerate(self._init_args):
            if not arg.is_real:
                all_real = False
            if not arg.is_rational:
                all_rational = False
            if not arg.is_integer:
                all_integer = False
            if not arg.is_natural:
                all_natural = False
            if arg.is_zero is None:
                all_nonzero = False
            if arg.is_even:
                count_even += 1
            if arg.is_even is False:
                count_odd += 1
            if arg.is_zero:
                exists_zero = True
                all_nonzero = False
            if arg.is_nonpositive:
                count_nonpositive += 1
            if arg.is_nonnegative:
                count_nonnegative += 1

        if all_real:
            self.is_real = True
            if exists_zero:
                self.is_zero = True
            elif all_nonzero:
                self.is_zero = False
        self.is_rational = ternary_or(all_rational, None)
        self.is_integer = ternary_or(all_integer, None)
        self.is_natural = ternary_or(all_natural, None)
        if (
            count_nonpositive % 2 == 0
            and count_nonnegative == total_args - count_nonpositive
        ):
            self.is_nonnegative = True
        if (
            count_nonpositive % 2 == 1
            and count_nonnegative == total_args - count_nonpositive
        ):
            self.is_nonpositive = True
        if count_even > 0 and count_even + count_odd == total_args:
            self.is_even = True
        if count_odd == total_args:
            self.is_even = False

    def evaluate(self) -> Mul:
        from pylogic.sympy_helpers import sympy_to_pylogic

        return sympy_to_pylogic(self.to_sympy())

    def to_sympy(self) -> sp.Mul:
        return sp.Mul(*[to_sympy(arg) for arg in self.args])

    def _latex(self) -> str:
        from pylogic.constant import Constant

        wrap = lambda p: (
            rf"\left({p._latex()}\right)"
            if not p.is_atomic
            and not p._is_wrapped
            and p.__class__._precedence >= self.__class__._precedence
            else p._latex()
        )
        s = ""
        last_was_minus = False
        for a in self.args:
            if a == Constant(-1):
                s += "{-"
                last_was_minus = True
            else:
                if last_was_minus:
                    s += f"{wrap(a)}}}"
                elif len(s) == 0:
                    s += wrap(a)
                else:
                    s += rf" \cdot {wrap(a)}"
                last_was_minus = False
        if last_was_minus:
            s += "1}"
        return s

    def __str__(self) -> str:
        wrap = lambda p: (
            f"({p})"
            if not p.is_atomic and p.__class__._precedence >= self.__class__._precedence
            else str(p)
        )
        s = ""
        last_was_minus = False
        for a in self.args:
            if a == -1:
                s += "-"
                last_was_minus = True
            else:
                if last_was_minus or len(s) == 0:
                    s += wrap(a)
                else:
                    s += f" * {wrap(a)}"
                last_was_minus = False
        if last_was_minus:
            s += "1"
        return s


class Pow(Expr):
    # order of operations for expressions (0-indexed)
    # Function MinElement Abs SequenceTerm Pow Prod Mul Sum Add Binary_Expr
    # Custom_Expr Piecewise Relation(eg <, subset)
    _precedence = 4

    def __init__(self, base: PBasic | Expr, exp: PBasic | Expr):
        super().__init__(base, exp)
        self.base = self.args[0]
        self.exp = self.args[1]

        if self.base.is_zero and self.exp.is_positive:
            self.is_zero = True
        if self.base.is_nonnegative and self.exp.is_nonnegative:
            self.is_nonnegative = True
        if self.base.is_positive and (self.exp.is_even is False):
            self.is_zero = False
            self.is_nonnegative = True
        if self.base.is_nonpositive and self.exp.is_even:
            self.is_nonnegative = True
        if self.base.is_negative and (self.exp.is_even is False):
            self.is_zero = False
            self.is_nonpositive = True

        if self.base.is_real and self.exp.is_positive:
            self.is_real = True

        if self.base.is_zero is False:
            if self.exp.is_even:
                self.is_zero = False
                self.is_nonnegative = True

            if self.base.is_real and self.exp.is_integer:
                self.is_real = True
            if self.base.is_integer and self.exp.is_even:
                self.is_natural = True
            if self.base.is_integer and self.exp.is_natural:
                self.is_integer = True
            if self.base.is_rational and self.exp.is_integer:
                self.is_rational = True
            if self.base.is_natural and self.exp.is_natural:
                self.is_natural = True

    def evaluate(self) -> Pow:
        from pylogic.sympy_helpers import sympy_to_pylogic

        return sympy_to_pylogic(self.to_sympy())

    def to_sympy(self) -> sp.Pow:
        return sp.Pow(to_sympy(self.base), to_sympy(self.exp))

    def _latex(self) -> str:
        if (
            self.base.is_atomic
            or self.base._is_wrapped
            or self.base.__class__._precedence <= self.__class__._precedence
        ):
            base_latex = self.base._latex()
        else:
            base_latex = rf"\left({latex(self.base)}\right)"
        exp_latex = self.exp._latex()
        return f"{base_latex}^{{{exp_latex}}}"

    def __str__(self) -> str:
        if self.base.is_atomic:
            base_str = str(self.base)
        else:
            base_str = f"({self.base})"
        return f"{base_str}^{self.exp}"


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
