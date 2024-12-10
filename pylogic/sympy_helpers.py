from __future__ import annotations

from fractions import Fraction
from typing import TYPE_CHECKING, Any, TypeVar, overload

import sympy as sp
from sympy.core.function import UndefinedFunction
from sympy.functions.elementary.piecewise import ExprCondPair, Piecewise
from sympy.logic.boolalg import And as SpAnd
from sympy.logic.boolalg import Not as SpNot
from sympy.logic.boolalg import Or as SpOr
from sympy.series.sequences import SeqBase, SeqFormula, SeqPer

from pylogic.constant import Constant, Infinity
from pylogic.expressions.abs import Abs
from pylogic.expressions.expr import Add, CustomExpr, Expr, Mul, Pow
from pylogic.expressions.function import CalledFunction
from pylogic.expressions.mod import Mod
from pylogic.expressions.piecewise import (
    OtherwiseBranch,
    PiecewiseBranch,
    PiecewiseExpr,
)
from pylogic.expressions.prod import Prod
from pylogic.expressions.sequence_term import SequenceTerm
from pylogic.expressions.sum import Sum
from pylogic.proposition.and_ import And
from pylogic.proposition.iff import Iff
from pylogic.proposition.implies import Implies
from pylogic.proposition.not_ import Not
from pylogic.proposition.or_ import Or
from pylogic.proposition.ordering.greaterorequal import GreaterOrEqual
from pylogic.proposition.ordering.greaterthan import GreaterThan
from pylogic.proposition.ordering.lessorequal import LessOrEqual
from pylogic.proposition.ordering.lessthan import LessThan
from pylogic.proposition.relation.equals import Equals
from pylogic.structures.sequence import (
    FiniteSequence,
    Pair,
    PeriodicSequence,
    Sequence,
    Triple,
)
from pylogic.structures.set_ import Set
from pylogic.symbol import Symbol
from pylogic.variable import Variable

if TYPE_CHECKING:

    class Basic(sp.Basic):
        _pyl_init_args: tuple[Any, ...]
        _pyl_init_kwargs: dict[str, Any]
        _pyl_class: type | None

    B = TypeVar("B", bound=Basic)
    tB = TypeVar("tB", bound=type[Basic])
else:
    B = TypeVar("B")
    tB = TypeVar("tB")


def _create_sympy_class(name: str, base: tB) -> tB:
    def _new(
        cls,
        *args,
        _pyl_class: type | None = None,
        _pyl_init_args: tuple | None = None,
        _pyl_init_kwargs: dict[str, Any] | None = None,
        **kwargs,
    ):
        val = base.__new__(cls, *args, **kwargs)
        if _pyl_class is None:
            s = f"Must provide _pyl_class for {cls}\nbase: {base}\n"
            s += f"args: {args}\nkwargs: {kwargs}"
            raise ValueError(s)
        val._pyl_class = _pyl_class
        val._pyl_init_args = _pyl_init_args or ()
        val._pyl_init_kwargs = _pyl_init_kwargs or {}
        return val

    return type(name, (base,), {"__new__": _new})  # type: ignore


PylSympySymbol = _create_sympy_class("PylSympySymbol", sp.Symbol)
PylSympySet = _create_sympy_class("PylSympySet", sp.Set)
PylSympySeqBase = _create_sympy_class("PylSympySeqBase", SeqBase)
PylSympySeqFormula = _create_sympy_class("PylSympySeqFormula", SeqFormula)
PylSympyExpr = _create_sympy_class("PylSympyExpr", sp.Function("CustomExpr"))
PylSympyFunction = _create_sympy_class("PylSympyFunction", UndefinedFunction)
PylSympyExprCondPair = _create_sympy_class("PylSympyExprCondPair", ExprCondPair)


class ToSympyError(ValueError):
    pass


class FromSympyError(ValueError):
    pass


SYMPY_ASSUMPTIONS = {
    "real",
    "rational",
    "integer",
    "even",
    "odd",
    "zero",
    "nonpositive",
    "nonnegative",
    "positive",
    "negative",
}


@overload
def sympy_to_pylogic(expr: sp.Integer) -> Constant[int]: ...
@overload
def sympy_to_pylogic(expr: sp.Float) -> Constant[float]: ...
@overload
def sympy_to_pylogic(expr: sp.Rational) -> Constant[Fraction]: ...
@overload
def sympy_to_pylogic(expr: sp.Add) -> Add: ...
@overload
def sympy_to_pylogic(expr: sp.Mul) -> Mul: ...
@overload
def sympy_to_pylogic(expr: sp.Pow) -> Pow: ...
@overload
def sympy_to_pylogic(expr: sp.Abs) -> Abs: ...
@overload
def sympy_to_pylogic(expr: SeqFormula) -> Sequence: ...
@overload
def sympy_to_pylogic(expr: SeqPer) -> PeriodicSequence: ...
@overload
def sympy_to_pylogic(expr: sp.Set) -> Set: ...
@overload
def sympy_to_pylogic(expr: sp.Symbol) -> Symbol: ...
@overload
def sympy_to_pylogic(expr: sp.Expr) -> CustomExpr: ...
def sympy_to_pylogic(expr: sp.Basic) -> Set | Sequence | Expr | Symbol:
    """
    Can only convert sympy expressions that are supported by pylogic.
    """
    from pylogic.structures.sequence import FiniteSequence, PeriodicSequence, Sequence
    from pylogic.structures.set_ import Set

    # TODO: Add support for more expressions
    match expr:
        case sp.oo:
            return Infinity
        case sp.Integer():
            return Constant(int(expr))
        case sp.Float():
            return Constant(float(expr))
        case sp.Rational():
            return Constant(Fraction(expr.p, expr.q))
        case sp.Add():
            return Add(*[sympy_to_pylogic(arg) for arg in expr.args])
        case sp.Mul():
            return Mul(*[sympy_to_pylogic(arg) for arg in expr.args])
        case sp.Pow():
            return Pow(*[sympy_to_pylogic(arg) for arg in expr.args])
        case sp.Abs():
            return Abs(sympy_to_pylogic(expr.args[0]))
        case sp.Mod():
            return Mod(sympy_to_pylogic(expr.args[0]), sympy_to_pylogic(expr.args[1]))
        case (
            PylSympySet()
            | PylSympySymbol()
            | PylSympySeqBase()
            | PylSympySeqFormula()
            | PylSympyExpr()
            | PylSympyFunction()
        ):
            return expr._pyl_class(*expr._pyl_init_args, **expr._pyl_init_kwargs)
        case ExprCondPair():
            if expr[1] == True:
                return OtherwiseBranch(sympy_to_pylogic(expr[0]))
            return PiecewiseBranch(sympy_to_pylogic(expr[1]), sympy_to_pylogic(expr[0]))
        case Piecewise():
            return PiecewiseExpr(*[sympy_to_pylogic(branch) for branch in expr.args])
        case sp.Product() | sp.Sum():
            nth_term, limits = expr.args
            nth_term_ = sympy_to_pylogic(nth_term)
            var, start, end = map(sympy_to_pylogic, limits[0])
            if start == 1:
                nth_term = lambda n: nth_term_.replace({var: n})
            else:
                nth_term = lambda n: nth_term_.replace({var: n + start - 1})
            if end == Infinity:
                seq = Sequence("sp", nth_term=nth_term, real=True)
            else:
                size = (end - start + 1).evaluate()
                seq = FiniteSequence("sp", nth_term=nth_term, length=size)
            return Prod(seq) if isinstance(expr, sp.Product) else Sum(seq)
        case sp.LessThan():
            return LessOrEqual(sympy_to_pylogic(expr.lhs), sympy_to_pylogic(expr.rhs))
        case sp.StrictLessThan():
            return LessThan(sympy_to_pylogic(expr.lhs), sympy_to_pylogic(expr.rhs))
        case sp.GreaterThan():
            return GreaterOrEqual(
                sympy_to_pylogic(expr.lhs), sympy_to_pylogic(expr.rhs)
            )
        case sp.StrictGreaterThan():
            return GreaterThan(sympy_to_pylogic(expr.lhs), sympy_to_pylogic(expr.rhs))
        case SpAnd():
            return And(*[sympy_to_pylogic(arg) for arg in expr.args])
        case SpOr():
            return Or(*[sympy_to_pylogic(arg) for arg in expr.args])
        case SpNot():
            return Not(sympy_to_pylogic(expr.args[0]))
        case sp.Eq():
            return Equals(sympy_to_pylogic(expr.lhs), sympy_to_pylogic(expr.rhs))
        case sp.Unequality():
            return Not(Equals(sympy_to_pylogic(expr.lhs), sympy_to_pylogic(expr.rhs)))
        case sp.Implies():
            return Implies(
                sympy_to_pylogic(expr.args[0]), sympy_to_pylogic(expr.args[1])
            )
        case sp.Equivalent():
            return Iff(sympy_to_pylogic(expr.args[0]), sympy_to_pylogic(expr.args[1]))
        case SeqFormula():
            if isinstance(expr.interval, sp.FiniteSet):
                ind = list(expr.interval)[0]
                return FiniteSequence(
                    "sp", length=1, initial_terms=[sympy_to_pylogic(expr.coeff(ind))]
                )
            if expr.interval.right.is_infinite or expr.interval.left.is_infinite:  # type: ignore
                return Sequence(
                    "sp", nth_term=lambda n: sympy_to_pylogic(expr.coeff(n))
                )
            else:
                # interval is bounded both ends
                return FiniteSequence(
                    "sp",
                    nth_term=lambda n: sympy_to_pylogic(expr.coeff(n)),
                    length=int(expr.interval.right - expr.interval.left + 1),  # type: ignore
                )
        case SeqPer():
            return PeriodicSequence(
                "sp",
                initial_terms=list(map(int, expr.periodical)),  # type: ignore
                period=int(expr.period),
            )
        case sp.Expr():
            return CustomExpr(
                "SympyCustomExpr",
                *[sympy_to_pylogic(arg) for arg in expr.args],  # type: ignore
            )
        case sp.Basic():
            # check for UndefinedFunction instance instance
            # the hierarchy in this case is
            # expr: expr.__class__: UndefinedFunction: type
            # where expr.__class__ was dynamically created and inherits from Basic
            if isinstance(expr.__class__, PylSympyFunction):
                return CalledFunction(
                    sympy_to_pylogic(expr.__class__),
                    *[sympy_to_pylogic(arg) for arg in expr.args],
                )
            raise FromSympyError(f"Unsupported sympy expression: {expr}")

        case _:
            raise FromSympyError(f"Unsupported sympy expression: {expr}")
