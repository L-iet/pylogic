from __future__ import annotations
from pylogic.proposition.proposition import Proposition
from pylogic.proposition.quantified.quantified import _Quantified
from typing import TYPE_CHECKING, Self

if TYPE_CHECKING:
    from sympy import Basic as SympyExpression
    from pylogic.set.sets import Set
from sympy.printing.latex import LatexPrinter
import sympy as sp


class Forall(_Quantified):
    def __init__(
        self,
        quantified_arg: Set | SympyExpression,
        inner_proposition: Proposition,
        is_assumption: bool = False,
        show_arg_position_names: bool = False,
        _is_proven: bool = False,
    ) -> None:
        q_arg = ("arg0", quantified_arg)
        assert quantified_arg.is_arbitrary, f"{quantified_arg} is not arbitrary"
        super().__init__(
            "forall",
            inner_proposition,
            is_assumption,
            quantified_arg=q_arg,
            show_arg_position_names=show_arg_position_names,
            _is_proven=_is_proven,
        )
        self.quantified_arg_value = self.quantified_arg[1]

    def copy(self):
        return super().copy(self)

    def hence_matrices_are_equal(self) -> "Equals":
        """
        Logical tactic.
        If self is a proven proposition of the form
        forall i: forall j: forall k:...: A[i, j, k...] = B[i, j, k...],
        returns a proven proposition of the form A = B.
        Note that the indices must appear in the same order in the foralls.
        """
        assert self.is_proven, f"{self} is not proven"
        indices = []
        prop = self
        while isinstance(prop, Forall):
            assert (
                prop.quantified_arg_value.is_integer
            ), f"{prop.quantified_arg} is not an integer"
            # maybe also check for is nonnegative
            indices.append(prop.quantified_arg_value)
            prop = prop.inner_proposition
        assert isinstance(prop, Equals), f"{prop} is not an equality"
        MatEl = sp.matrices.expressions.matexpr.MatrixElement
        assert isinstance(prop.left, MatEl) and isinstance(
            prop.right, MatEl
        ), f"The inner equality {prop} is not between matrix elements"
        left_mat, *left_indices = prop.left.args
        right_mat, *right_indices = prop.right.args
        for i, index in enumerate(indices):
            assert (
                index == left_indices[i] == right_indices[i]
            ), f"Indices mismatch: {index}, {left_indices[i]}, {right_indices[i]}"
        new_p = Equals(left_mat, right_mat)
        new_p._is_proven = True
        return new_p
