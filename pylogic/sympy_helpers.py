from __future__ import annotations

from fractions import Fraction
from typing import TYPE_CHECKING, Any, TypeVar, overload

import sympy as sp
from sympy.series.sequences import SeqBase, SeqFormula, SeqPer

from pylogic.constant import Constant
from pylogic.expressions.abs import Abs
from pylogic.expressions.expr import Add, CustomExpr, Expr, Mul, Pow
from pylogic.expressions.sequence_term import SequenceTerm
from pylogic.symbol import Symbol
from pylogic.variable import Variable

B = TypeVar("B", bound=sp.Basic)

if TYPE_CHECKING:
    from pylogic.structures.sequence import PeriodicSequence, Sequence
    from pylogic.structures.set_ import Set


class PylSympySymbol(sp.Symbol):
    _pyl_init_args: tuple[Any, ...]
    _pyl_init_kwargs: dict[str, Any]
    _pyl_class: str | None

    def __new__(
        cls,
        *args,
        _pyl_class: str | None = None,
        _pyl_init_args: tuple | None = None,
        _pyl_init_kwargs: dict[str, Any] | None = None,
        **kwargs,
    ) -> PylSympySymbol:
        val = super().__new__(cls, *args, **kwargs)
        val._pyl_class = _pyl_class
        val._pyl_init_args = _pyl_init_args or ()
        val._pyl_init_kwargs = _pyl_init_kwargs or {}
        return val


class PylSympySet(sp.Set):
    _pyl_init_args: tuple[Any, ...]
    _pyl_init_kwargs: dict[str, Any]
    _pyl_class: str | None

    def __new__(
        cls,
        *args,
        _pyl_class: str | None = None,
        _pyl_init_args: tuple | None = None,
        _pyl_init_kwargs: dict[str, Any] | None = None,
        **kwargs,
    ) -> PylSympySet:
        val = super().__new__(cls, *args, **kwargs)
        val._pyl_class = _pyl_class
        val._pyl_init_args = _pyl_init_args or ()
        val._pyl_init_kwargs = _pyl_init_kwargs or {}
        return val


class PylSympySeqBase(SeqBase):
    _pyl_init_args: tuple[Any, ...]
    _pyl_init_kwargs: dict[str, Any]
    _pyl_class: str | None

    def __new__(
        cls,
        *args,
        _pyl_class: str | None = None,
        _pyl_init_args: tuple | None = None,
        _pyl_init_kwargs: dict[str, Any] | None = None,
        **kwargs,
    ) -> PylSympySeqBase:
        val = super().__new__(cls, *args, **kwargs)
        val._pyl_class = _pyl_class
        val._pyl_init_args = _pyl_init_args or ()
        val._pyl_init_kwargs = _pyl_init_kwargs or {}
        return val


class PylSympySeqFormula(SeqFormula):
    _pyl_init_args: tuple[Any, ...]
    _pyl_init_kwargs: dict[str, Any]
    _pyl_class: str | None

    def __new__(
        cls,
        *args,
        _pyl_class: str | None = None,
        _pyl_init_args: tuple | None = None,
        _pyl_init_kwargs: dict[str, Any] | None = None,
        **kwargs,
    ) -> PylSympySeqFormula:
        val = super().__new__(cls, *args, **kwargs)
        val._pyl_class = _pyl_class
        val._pyl_init_args = _pyl_init_args or ()
        val._pyl_init_kwargs = _pyl_init_kwargs or {}
        return val


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
def sympy_to_pylogic(expr: PylSympySymbol) -> Symbol: ...
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
        case SeqFormula():
            if isinstance(expr.interval, sp.FiniteSet):
                ind = list(expr.interval)[0]
                return FiniteSequence("sp", [sympy_to_pylogic(expr.coeff(ind))], 1)
            if expr.interval.right.is_infinite or expr.interval.left.is_infinite:  # type: ignore
                return Sequence(
                    "sp", nth_term=lambda n: sympy_to_pylogic(expr.coeff(n))
                )
            else:
                # interval is bounded both ends
                return FiniteSequence(
                    "sp",
                    nth_term=lambda n: sympy_to_pylogic(expr.coeff(n)),
                    size=int(expr.interval.right - expr.interval.left + 1),  # type: ignore
                )
        case SeqPer():
            return PeriodicSequence(
                "sp",
                initial_terms=list(map(int, expr.periodical)),  # type: ignore
                period=int(expr.period),
            )
        case sp.Set():
            return Set(repr(expr))
        case PylSympySymbol():
            if expr._pyl_class == "Variable":
                return Variable(
                    expr.name, *expr._pyl_init_args, **expr._pyl_init_kwargs
                )
            elif expr._pyl_class == "Constant":
                return Constant(
                    expr.name, *expr._pyl_init_args, **expr._pyl_init_kwargs
                )
            elif expr._pyl_class == "SequenceTerm":
                return SequenceTerm(*expr._pyl_init_args, **expr._pyl_init_kwargs)
            else:
                raise ValueError(f"Unsupported _pyl_class: {expr._pyl_class}")
        case sp.Expr():
            return CustomExpr(
                "SympyCustomExpr",
                *[sympy_to_pylogic(arg) for arg in expr.args],  # type: ignore
            )
        case _:
            raise ValueError(f"Unsupported sympy expression: {expr}")
