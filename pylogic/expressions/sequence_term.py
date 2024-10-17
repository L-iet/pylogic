from __future__ import annotations

from typing import TYPE_CHECKING, Generic, Self, TypeVar

from pylogic import Term
from pylogic.expressions.expr import Expr
from pylogic.structures.sequence import Sequence

if TYPE_CHECKING:
    from pylogic.proposition.relation.contains import IsContainedIn
    from pylogic.sympy_helpers import PylSympySymbol

T = TypeVar("T", bound=Term)


class SequenceTerm(Expr, Generic[T]):
    def __init__(self, sequence: Sequence[T], index: Term) -> None:
        super().__init__(sequence, index)
        self.sequence: Sequence[T] = sequence
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

    def to_sympy(self) -> PylSympySymbol:
        from pylogic.sympy_helpers import PylSympySymbol

        return PylSympySymbol(
            *self._init_args,
            _pyl_class=self.__class__.__name__,
            _pyl_init_args=self._init_args,
            _pyl_init_kwargs=self._init_kwargs,
            **self._init_kwargs,
        )

    def _latex(self) -> str:
        return f"{self.sequence.name}_{{{self.index}}}"

    def __str__(self) -> str:
        return self.name
