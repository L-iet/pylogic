from __future__ import annotations

from typing import TYPE_CHECKING

from pylogic.expressions.expr import Expr

if TYPE_CHECKING:
    import sympy as sp

    from pylogic.constant import Constant
    from pylogic.structures.sequence import Sequence


class Prod(Expr):
    """
    Represents a product of a sequence of non-set terms.
    For products of sets, see pylogic.structures.set_.CartesProduct
    """

    # order of operations for expressions (0-indexed)
    # Function MinElement Abs SequenceTerm Pow Prod Mul Sum Add Binary_Expr
    # Custom_Expr Piecewise Relation(eg <, subset)
    _precedence = 5
    _is_wrapped = True

    def __init__(self, sequence: Sequence) -> None:
        self.sequence = sequence
        super().__init__(sequence)

    def evaluate(self) -> Prod | Constant:
        # TODO
        return self

    def to_sympy(self) -> sp.Basic:
        raise NotImplementedError

    def _latex(self) -> str:
        return rf"\prod {self.sequence._latex()}"

    def __str__(self) -> str:
        return f"Prod({self.sequence})"
