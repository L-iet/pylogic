from __future__ import annotations

from fractions import Fraction
from typing import TYPE_CHECKING

import sympy as sp

from pylogic import Term
from pylogic.expressions.expr import Expr, to_sympy

if TYPE_CHECKING:
    from pylogic.constant import Constant


class MinElement(Expr):
    def __init__(self, expr: Term) -> None:
        self.expr = expr
        super().__init__(expr)

    def evaluate(self) -> MinElement | Term:
        from pylogic.helpers import getkey
        from pylogic.proposition.not_ import Not
        from pylogic.proposition.relation.subsets import IsSubsetOf
        from pylogic.structures.set_ import EmptySet, Set
        from pylogic.theories.natural_numbers import Naturals
        from pylogic.theories.real_analysis import Interval
        from pylogic.variable import Variable

        # check if it is an interval of reals closed below
        if isinstance(self.expr, Interval) and self.expr.a_inclusive:
            return self.expr.a

        # check if it is a nonempty subset of naturals
        elif isinstance(self.expr, (Set, Variable)):
            subset_proof = getkey(
                self.expr.knowledge_base, IsSubsetOf(self.expr, Naturals), default=None
            )
            if subset_proof is not None:
                non_empty_proof = getkey(
                    self.expr.knowledge_base, Not(self.expr.equals(EmptySet))
                )
                exists_min_proof = Naturals.well_ordering_set(self.expr)(
                    subset_proof, non_empty_proof
                )
                min_, _ = exists_min_proof.extract()
                return min_
        return self

    def to_sympy(self) -> sp.Basic:
        raise NotImplementedError

    def _latex(self) -> str:
        return rf"\text{{MinElement}}\left({self.expr}\right)"

    def __str__(self) -> str:
        return f"MinElement({self.expr})"
