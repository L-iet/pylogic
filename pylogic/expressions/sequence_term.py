from __future__ import annotations

from typing import TYPE_CHECKING, Generic, Self, TypeVar

from pylogic.expressions.expr import Expr
from pylogic.typing import Term

if TYPE_CHECKING:
    import sympy as sp

    from pylogic.proposition.relation.contains import IsContainedIn
    from pylogic.structures.sequence import Sequence
    from pylogic.sympy_helpers import PylSympySymbol
    from pylogic.variable import Variable

T = TypeVar("T", bound=Term)


class SequenceTerm(Expr, Generic[T]):
    # order of operations for expressions (0-indexed)
    # Function MinElement Abs SequenceTerm Pow Prod Mul Sum Add Binary_Expr
    # Custom_Expr Piecewise Relation(eg <, subset)
    _precedence = 3
    _is_wrapped = True

    def __init__(self, *args, **kwargs) -> None:
        super().__init__(*args, **kwargs)
        self.mutable_attrs_to_copy = self.mutable_attrs_to_copy + [
            "sequence",
            "index",
            "name",
            "elements",
        ]

    def __new_init__(self, sequence: Sequence[T] | Variable, index: Term) -> None:
        super().__new_init__(sequence, index)
        self.sequence: Sequence[T] | Variable = self.args[0]  # type: ignore
        self.sequence.parent_exprs.append(self)
        self.index = self.args[1]

        # for sequence of sets.
        self.name = f"{self.sequence.name}_({self.index})"
        self.elements = set()
        self.is_cartes_power: bool | None = None
        self.is_cartes_product: bool | None = None
        self.is_empty: bool | None = None
        self.is_intersection: bool | None = None
        self.is_union: bool | None = None

    def update_properties(self) -> None:
        sequence = self.args[0]
        self.is_real = sequence.is_real
        self.is_rational = sequence.is_rational
        self.is_integer = sequence.is_integer
        self.is_natural = sequence.is_natural
        self.is_zero = sequence.is_zero
        self.is_even = sequence.is_even
        self.is_odd = sequence.is_odd
        self.is_nonnegative = sequence.is_nonnegative
        self.is_nonpositive = sequence.is_nonpositive
        self.is_set = sequence.is_set

    def predicate(self, term: Term) -> IsContainedIn:
        """
        For sequences of sets.
        """
        from pylogic.proposition.relation.contains import IsContainedIn

        return IsContainedIn(term, self)

    def contains(self, term: Term, **kwargs) -> IsContainedIn:
        """
        For sequences of sets.
        """
        from pylogic.proposition.relation.contains import IsContainedIn

        return IsContainedIn(term, self, **kwargs)

    def evaluate(self, **kwargs) -> SequenceTerm | T:
        from pylogic.variable import Variable

        if isinstance(self.sequence, Variable):
            return self
        from pylogic.constant import Constant

        indx = self.index.evaluate()
        if indx in self.sequence.terms:
            return self.sequence.terms[indx]
        elif self.sequence.nth_term and indx.is_natural:
            if isinstance(indx, Constant) and isinstance(indx.value, int):
                self.sequence.terms[indx] = self.sequence.nth_term(indx)
                res = self.sequence.terms[indx]
            else:
                res = self.sequence.nth_term(indx)
            if getattr(res, "is_set", False):
                self._is_set = True
                self.is_cartes_power = res.is_cartes_power
                self.is_cartes_product = res.is_cartes_product
                self.is_empty = res.is_empty
                self._is_finite = res.is_finite
                self.is_intersection = res.is_intersection
                self.is_union = res.is_union
            return res

        return SequenceTerm(self.sequence, indx)

    def _latex(self) -> str:
        return f"{{{self.sequence.name}}}_{{{self.index._latex()}}}"

    def __str__(self) -> str:
        return self.name
