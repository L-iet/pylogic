from __future__ import annotations

from sympy.concrete.products import Product
from sympy.core.mul import Mul

from pylogic.expressions.sum import _Aggregate
from pylogic.structures.sequence import Sequence


class Prod(_Aggregate):
    """
    Represents a product of a sequence of non-set terms.
    For products of sets, see pylogic.structures.set_.CartesProduct
    """

    # order of operations for expressions (0-indexed)
    # Function MinElement Abs SequenceTerm Pow Prod Mul Sum Add Binary_Expr
    # Custom_Expr Piecewise Relation(eg <, subset)
    _precedence = 5
    _is_wrapped = True

    def __new_init__(self, sequence: Sequence) -> None:
        super().__new_init__(sequence)

    def update_properties(self) -> None:
        from pylogic.helpers import ternary_and, ternary_or
        from pylogic.structures.sequence import FiniteSequence

        sequence = self.args[0]
        super().update_properties()
        self._is_nonnegative = ternary_or(
            sequence.is_nonnegative,
            ternary_and(
                isinstance(sequence, FiniteSequence),
                True if sequence.length is not None else None,
                sequence.length.is_even,
                sequence.is_nonpositive,
            ),
        )
        self._is_nonpositive = ternary_and(
            isinstance(sequence, FiniteSequence),
            True if sequence.length is not None else None,
            sequence.length.is_odd,
            sequence.is_nonpositive,
        )

    def to_sympy(self) -> Product | Mul:
        return super().to_sympy(_finite_class=Mul, _infinite_class=Product)  # type: ignore

    def _latex(self) -> str:
        return rf"\prod {self.sequence._latex()}"

    def __str__(self) -> str:
        return f"Prod({self.sequence})"
