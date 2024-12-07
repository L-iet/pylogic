from __future__ import annotations

from fractions import Fraction
from typing import TYPE_CHECKING

import sympy as sp

from pylogic.expressions.expr import Expr, to_sympy
from pylogic.typing import PBasic, PythonNumeric, Term

if TYPE_CHECKING:
    from pylogic.constant import Constant


class Gcd(Expr):
    """
    The greatest common divisor of two or more integers.
    """

    # order of operations for expressions (0-indexed)
    # Function MinElement Abs/gcd SequenceTerm Pow Prod Mul Sum Add Binary_Expr
    # Custom_Expr Piecewise Relation(eg <, subset)
    _precedence = 2

    _is_wrapped = True

    def __new_init__(self, *args: Expr | PBasic | PythonNumeric) -> None:
        from pylogic.inference import Inference
        from pylogic.theories.integers import Integers

        super().__new_init__(*args)
        self.update_properties()

        for arg in self.args:
            self.knowledge_base.add(
                Integers.divides(
                    self,
                    arg,
                    _is_proven=True,
                    _assumptions=set(),
                    _inference=Inference(None, rule="by_definition"),
                )
            )

    def evaluate(self, **kwargs) -> Term:
        from pylogic.sympy_helpers import FromSympyError, sympy_to_pylogic

        try:
            return sympy_to_pylogic(
                sp.gcd(*[to_sympy(expr.evaluate()) for expr in self.args])
            )
        except FromSympyError:
            return self

    def _latex(self) -> str:
        return f"\\gcd\\left({', '.join([expr._latex() for expr in self.args])}\\right)"

    def __str__(self) -> str:
        return f"gcd({', '.join([str(expr) for expr in self.args])})"

    def update_properties(self) -> None:
        from pylogic.helpers import ternary_and

        self.is_natural = ternary_and(*[expr.is_integer for expr in self.args])
        self.is_real = self._is_natural
        self.is_rational = self._is_natural
        self.is_integer = self._is_natural
        self.is_zero = False if self._is_natural else None
        self.is_even = ternary_and(*[expr.is_even for expr in self.args])
        self.is_nonnegative = True if self._is_natural else None
        self.is_nonpositive = self._is_zero
