from __future__ import annotations

from typing import TYPE_CHECKING

import sympy as sp

from pylogic import Term
from pylogic.expressions.expr import Expr

if TYPE_CHECKING:
    from pylogic.structures.sequence import Sequence


class _Aggregate(Expr):
    """
    Represents an aggregate of a sequence of non-set terms eg Sum, Product.
    """

    def __init__(self, sequence: Sequence) -> None:
        super().__init__(sequence)
        self.sequence = sequence
        self._is_real = sequence.is_real
        self._is_rational = sequence.is_rational
        self._is_integer = sequence.is_integer
        self._is_natural = sequence.is_natural
        self._is_zero = sequence.is_zero
        self._is_even = sequence.is_even

    def evaluate(self) -> Term:
        from pylogic.sympy_helpers import sympy_to_pylogic

        try:
            return sympy_to_pylogic(self.to_sympy().doit())
        except ValueError:
            return self

    def to_sympy(self, _finite_class=sp.Add, _infinite_class=sp.Sum) -> sp.Basic:
        from pylogic.structures.sequence import FiniteSequence
        from pylogic.variable import Variable

        if not self.sequence.is_real:
            raise ValueError(
                "Cannot convert to sympy object: The sequence must be real."
            )
        if (
            isinstance(self.sequence, FiniteSequence)
            and self.sequence.length is not None
        ):
            # if has an nth term, return a sympy aggregate
            if self.sequence.nth_term is not None:
                n = Variable("n")
                return _infinite_class(
                    self.sequence.nth_term(n).to_sympy(),
                    (n.to_sympy(), 1, self.sequence.length.to_sympy()),
                )
            elif self.sequence.length == len(self.sequence.initial_terms):
                # if length is int numeric and does not have an nth term, but length of initial terms matches length,
                # return a sympy finite aggregate
                return _finite_class(
                    *[term.to_sympy() for term in self.sequence.initial_terms]
                )

        # otherwise, raise an error
        raise ValueError(
            "Cannot convert to sympy object: The sequence must have a finite length and nth term."
        )


class Sum(_Aggregate):
    """
    Represents a sum of a sequence of non-set terms.
    For unions of sets, see pylogic.structures.set_.Union
    """

    # order of operations for expressions (0-indexed)
    # Function MinElement Abs SequenceTerm Pow Prod Mul Sum Add Binary_Expr
    # Custom_Expr Piecewise Relation(eg <, subset)
    _precedence = 7
    _is_wrapped = True

    def __init__(self, sequence: Sequence) -> None:
        super().__init__(sequence)
        self._is_nonnegative = sequence.is_nonnegative
        self._is_nonpositive = sequence.is_nonpositive

    def _latex(self) -> str:
        return rf"\sum {self.sequence._latex()}"

    def to_sympy(self) -> sp.Sum | sp.Add:
        return super().to_sympy(_finite_class=sp.Add, _infinite_class=sp.Sum)  # type: ignore

    def __str__(self) -> str:
        return f"Sum({self.sequence})"
