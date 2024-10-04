from __future__ import annotations

from typing import TYPE_CHECKING, Generic, Self, TypeVar

import sympy as sp

from pylogic import Term
from pylogic.expressions.expr import Expr, to_sympy
from pylogic.structures.sequence import Sequence

if TYPE_CHECKING:
    from pylogic.constant import Constant
    from pylogic.sympy_helpers import PylSympySymbol

T = TypeVar("T", bound=Term)


class SequenceTerm(Expr, Generic[T]):
    def __init__(self, sequence: Sequence[T], index: int | Constant[int]) -> None:
        self.sequence = sequence
        self.index = int(index)
        super().__init__(sequence, index)

    def evaluate(self) -> Self | T:
        if self.index in self.sequence.terms:
            return self.sequence.terms[self.index]
        elif self.sequence.nth_term:
            self.sequence.terms[self.index] = self.sequence.nth_term(self.index)
            return self.sequence.terms[self.index]
        return self

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
        return f"{self.sequence.name}_{self.index}"
