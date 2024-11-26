from __future__ import annotations

from fractions import Fraction
from typing import TYPE_CHECKING

import sympy as sp

from pylogic import PBasic, PythonNumeric, Term
from pylogic.expressions.expr import Expr, to_sympy

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

    def __init__(self, *args: Expr | PBasic | PythonNumeric) -> None:
        from pylogic.helpers import ternary_and
        from pylogic.inference import Inference
        from pylogic.theories.integers import Divides

        super().__init__(*args)
        self._is_real = ternary_and(*[expr.is_integer for expr in self.args])
        self._is_rational = self._is_real
        self._is_integer = self._is_real
        self._is_natural = self._is_real

        for arg in self.args:
            self.knowledge_base.add(
                Divides(
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

    def to_sympy(self) -> sp.Basic:
        from pylogic.sympy_helpers import PylSympyExpr

        return PylSympyExpr(
            "Gcd",
            *[to_sympy(expr) for expr in self.args],
            _pyl_class=self.__class__,
            _pyl_init_args=self._init_args,
            _pyl_init_kwargs=self._init_kwargs,
        )

    def _latex(self) -> str:
        return f"\\gcd\\left({', '.join([expr._latex() for expr in self.args])}\\right)"

    def __str__(self) -> str:
        return f"gcd({', '.join([str(expr) for expr in self.args])})"
