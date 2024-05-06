from __future__ import annotations
from typing import TYPE_CHECKING
from fractions import Fraction

import sympy as sp
from pylogic.expressions.expr import Expr, evaluate

if TYPE_CHECKING:
    from pylogic.symbol import Symbol

    Basic = Symbol | int | float | Fraction


class Abs(Expr):
    def __init__(self, expr: Expr | Basic) -> None:
        self.expr = expr
        super().__init__(expr)

    def evaluate(self) -> sp.Basic:
        return sp.Abs(evaluate(self.expr))

    def _latex(self) -> str:
        return rf"\left|{self.expr._latex()}\right|"

    def __str__(self) -> str:
        return f"|{self.expr}|"
