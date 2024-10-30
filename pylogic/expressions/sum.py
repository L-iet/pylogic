from __future__ import annotations

from typing import TYPE_CHECKING

from pylogic.expressions.expr import Expr

if TYPE_CHECKING:
    import sympy as sp

    from pylogic.constant import Constant
    from pylogic.structures.sequence import Sequence


class Sum(Expr):
    """
    Represents a sum of a sequence of non-set terms.
    For unions of sets, see pylogic.structures.set_.Union
    """

    def __init__(self, sequence: Sequence) -> None:
        self.sequence = sequence
        super().__init__(sequence)

    def evaluate(self) -> Sum | Constant:
        # TODO
        return self

    def to_sympy(self) -> sp.Basic:
        raise NotImplementedError

    def _latex(self) -> str:
        return rf"\sum {self.sequence._latex()}"

    def __str__(self) -> str:
        return f"Sum({self.sequence})"
