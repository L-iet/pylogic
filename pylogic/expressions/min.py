from __future__ import annotations

import sympy as sp

from pylogic.expressions.expr import Expr
from pylogic.typing import Term


class MinElement(Expr):
    # order of operations for expressions (0-indexed)
    # Function MinElement Abs SequenceTerm Pow Prod Mul Sum Add Binary_Expr
    # Custom_Expr Piecewise Relation(eg <, subset)
    _precedence = 1
    _is_wrapped = True

    def __init__(self, *args, **kwargs) -> None:
        super().__init__(*args, **kwargs)
        self.mutable_attrs_to_copy = self.mutable_attrs_to_copy + ["expr"]

    def __new_init__(self, expr: Term) -> None:
        self.expr = expr
        super().__new_init__(expr)

    def evaluate(self, **kwargs) -> MinElement | Term:
        from pylogic.helpers import getkey
        from pylogic.proposition.not_ import Not
        from pylogic.proposition.relation.subsets import IsSubsetOf
        from pylogic.structures.set_ import EmptySet, Set
        from pylogic.theories.natural_numbers import Naturals
        from pylogic.theories.real_numbers import Interval
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

    def _latex(self) -> str:
        return rf"\text{{MinElement}}\left({self.expr._latex()}\right)"

    def __str__(self) -> str:
        return f"MinElement({self.expr})"

    def update_properties(self) -> None:
        return
