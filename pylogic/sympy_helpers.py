from __future__ import annotations

from fractions import Fraction
from typing import Any, TypeVar, overload

import sympy as sp

from pylogic.constant import Constant
from pylogic.expressions.abs import Abs
from pylogic.expressions.expr import Add, CustomExpr, Expr, Mul, Pow
from pylogic.symbol import Symbol
from pylogic.variable import Variable

B = TypeVar("B", bound=sp.Basic)


class PylSympySymbol(sp.Symbol):
    _pyl_init_args: tuple[Any, ...]
    _pyl_init_kwargs: dict[str, Any]
    _pyl_class: str

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
def sympy_to_pylogic(expr: PylSympySymbol) -> Symbol: ...
@overload
def sympy_to_pylogic(expr: sp.Expr) -> CustomExpr: ...
def sympy_to_pylogic(expr: sp.Basic) -> Expr | Symbol:
    """
    Can only convert sympy expressions that are supported by pylogic.
    """
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
        case PylSympySymbol():
            if expr._pyl_class == "Variable":
                return Variable(
                    expr.name, *expr._pyl_init_args, **expr._pyl_init_kwargs
                )
            elif expr._pyl_class == "Constant":
                return Constant(
                    expr.name, *expr._pyl_init_args, **expr._pyl_init_kwargs
                )
            else:
                raise ValueError(f"Unsupported _pyl_class: {expr._pyl_class}")
        case sp.Expr():
            return CustomExpr(
                "SympyCustomExpr",
                *[sympy_to_pylogic(arg) for arg in expr.args],  # type: ignore
            )
        case _:
            raise ValueError(f"Unsupported sympy expression: {expr}")
