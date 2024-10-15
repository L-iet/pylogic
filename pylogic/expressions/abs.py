from __future__ import annotations

from fractions import Fraction
from typing import TYPE_CHECKING

import sympy as sp

from pylogic import Term
from pylogic.expressions.expr import Expr, to_sympy

if TYPE_CHECKING:
    from pylogic.constant import Constant


class Abs(Expr):
    def __init__(self, expr: Term) -> None:
        self.expr = expr
        super().__init__(expr)

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
        if isinstance(self.expr, (int, float, Fraction)):
            return rf"\left|{self.expr}\right|"
        return rf"\left|{self.expr._latex()}\right|"

    def __str__(self) -> str:
        return f"|{self.expr}|"
