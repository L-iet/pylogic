from __future__ import annotations

from typing import TYPE_CHECKING, Generic, Self, TypeVar

from pylogic import Term
from pylogic.expressions.expr import Expr

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
    is_atomic = True

    def __init__(self, sequence: Sequence[T] | Variable, index: Term) -> None:
        super().__init__(sequence, index)
        self.sequence: Sequence[T] | Variable = sequence
        self.index = self.args[1]

        # for sequence of sets.
        self.name = f"{self.sequence.name}_({self.index})"
        self.elements = set()
        self.is_cartes_power: bool | None = None
        self.is_cartes_product: bool | None = None
        self.is_empty: bool | None = None
        self.is_finite: bool | None = None
        self.is_intersection: bool | None = None
        self.is_set = None
        self.is_set_ = None
        self.is_union: bool | None = None

        self._is_real = self.sequence.is_real
        self._is_rational = self.sequence.is_rational
        self._is_integer = self.sequence.is_integer
        self._is_natural = self.sequence.is_natural
        self._is_zero = self.sequence.is_zero
        self._is_even = self.sequence.is_even
        self._is_nonnegative = self.sequence.is_nonnegative
        self._is_nonpositive = self.sequence.is_nonpositive

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

    def evaluate(self) -> SequenceTerm | T:
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
                self.is_set = True
                self.is_set_ = True
                self.is_cartes_power = res.is_cartes_power
                self.is_cartes_product = res.is_cartes_product
                self.is_empty = res.is_empty
                self.is_finite = res.is_finite
                self.is_intersection = res.is_intersection
                self.is_union = res.is_union
            return res

        return SequenceTerm(self.sequence, indx)

    def to_sympy(self) -> sp.Expr:
        from pylogic.sympy_helpers import PylSympyExpr

        return PylSympyExpr(
            "SequenceTerm",
            self.sequence.to_sympy(),
            self.index.to_sympy(),
            _pyl_class=self.__class__,
            _pyl_init_args=self._init_args,
            _pyl_init_kwargs=self._init_kwargs,
        )

    def _latex(self) -> str:
        return f"{{{self.sequence.name}}}_{{{self.index._latex()}}}"

    def __str__(self) -> str:
        return self.name
