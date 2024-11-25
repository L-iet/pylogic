from __future__ import annotations

from fractions import Fraction
from typing import TYPE_CHECKING

import sympy as sp

from pylogic import Term
from pylogic.expressions.expr import Expr, to_sympy

if TYPE_CHECKING:
    from pylogic.constant import Constant


class Abs(Expr):
    """
    A nonnegative real number representing the size of some object.
    """

    # order of operations for expressions (0-indexed)
    # Function MinElement Abs SequenceTerm Pow Prod Mul Sum Add Binary_Expr
    # Custom_Expr Piecewise Relation(eg <, subset)
    _precedence = 2

    _is_wrapped = True

    def __init__(self, expr: Term) -> None:
        from pylogic.helpers import ternary_or

        super().__init__(expr)
        self.expr = expr
        self._is_real = True
        self._is_rational = expr.is_rational
        self._is_integer = expr.is_integer
        self._is_natural = ternary_or(expr.is_natural, expr.is_integer)
        self._is_zero = True if expr.is_zero else None
        self._is_even = expr.is_even
        self._is_nonnegative = True
        self._is_nonpositive = self.is_zero

    def evaluate(self) -> Abs | Constant:
        from pylogic.helpers import is_python_numeric
        from pylogic.symbol import Symbol

        if is_python_numeric(self.expr):
            return Constant(abs(self.expr))  # type: ignore
        elif isinstance(self.expr, (Expr, Symbol)):
            return Abs(self.expr.evaluate())
        return self

    def to_sympy(self) -> sp.Basic:
        return sp.Abs(to_sympy(self.expr))

    def _latex(self) -> str:
        return f"\\left|{self.expr._latex()}\\right|"

    def __str__(self) -> str:
        return f"|{self.expr}|"
