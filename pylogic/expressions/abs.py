from __future__ import annotations

from fractions import Fraction
from typing import TYPE_CHECKING

import sympy as sp

from pylogic.expressions.expr import Expr, to_sympy
from pylogic.typing import Term

if TYPE_CHECKING:
    from pylogic.constant import Constant


class Abs(Expr):
    """
    A nonnegative real number representing the size of some object.
    """

    _precedence = 2

    _is_wrapped = True

    def __init__(self, *args, **kwargs) -> None:
        super().__init__(*args, **kwargs)
        self.mutable_attrs_to_copy = self.mutable_attrs_to_copy + ["expr"]

    def __new_init__(self, expr: Term) -> None:
        super().__new_init__(expr)
        self.expr = self.args[0]

    def update_properties(self) -> None:
        from pylogic.helpers import ternary_or

        self.is_real = True
        self.is_rational = self.args[0].is_rational
        self.is_integer = self.args[0].is_integer
        self.is_natural = ternary_or(self.args[0].is_natural, self.args[0].is_integer)
        self.is_zero = True if self.args[0].is_zero else None
        self.is_even = self.args[0].is_even
        self.is_odd = self.args[0].is_odd
        self.is_nonnegative = True
        self.is_nonpositive = self.is_zero

    def evaluate(self, **kwargs) -> Abs | Constant:
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
