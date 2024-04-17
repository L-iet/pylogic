from __future__ import annotations
from typing import TYPE_CHECKING, Self, TypeVar, TypedDict

from pylogic.proposition.proposition import Proposition
from pylogic.proposition.quantified.quantified import _Quantified
from pylogic.proposition.implies import Implies


if TYPE_CHECKING:
    from sympy import Basic as SympyExpression
    from pylogic.proposition.relation.equals import Equals
    from pylogic.variable import Variable
    from pylogic.proposition.quantified.exists import Exists
from sympy.printing.latex import LatexPrinter
import sympy as sp

TProposition = TypeVar("TProposition", bound="Proposition")
UProposition = TypeVar("UProposition", bound="Proposition")
B = TypeVar("B", bound="Proposition")
Tactic = TypedDict("Tactic", {"name": str, "arguments": list[str]})


class Forall(_Quantified[TProposition]):
    tactics: list[Tactic] = [
        {"name": "quantified_modus_ponens", "arguments": ["Implies"]},
        {"name": "hence_matrices_are_equal", "arguments": []},
    ]

    def __init__(
        self,
        variable: Variable,
        inner_proposition: TProposition,
        is_assumption: bool = False,
        _is_proven: bool = False,
    ) -> None:
        super().__init__(
            "forall",
            variable,
            inner_proposition,
            is_assumption,
            _is_proven=_is_proven,
        )

    def __eq__(self, other: Proposition) -> bool:
        if isinstance(other, Forall):
            return self.inner_proposition == other.inner_proposition
        return False

    def copy(self) -> Self:
        return self.__class__(
            self.variable.copy(),
            self.inner_proposition.copy(),
            self.is_assumption,
            self.is_proven,
        )

    def hence_matrices_are_equal(self) -> Equals:
        """
        Logical tactic.
        If self is a proven proposition of the form
        forall i: forall j: forall k:...: A[i, j, k...] = B[i, j, k...],
        returns a proven proposition of the form A = B.
        Note that the indices must appear in the same order in the foralls.
        """
        assert self.is_proven, f"{self} is not proven"
        indices: list[Variable] = []
        prop = self
        while isinstance(prop, Forall):
            # TODO: check why is_integer is not seen
            assert prop.variable.is_integer, f"{prop.variable} is not an integer"  # type: ignore
            # maybe also check for is nonnegative
            indices.append(prop.variable)
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

    def quantified_modus_ponens(
        self, other: Forall[Implies[TProposition, B]] | Exists[Implies[TProposition, B]]
    ) -> Forall[B] | Exists[B]:
        """
        Logical tactic. If self is forall x: P(x) and given forall x: P(x) -> Q(x)
        (or exists x: P(x) -> Q(x)), and each is proven, conclude
        forall x: Q(x) (or exists x: Q(x)).
        """
        from pylogic.proposition.quantified.exists import Exists

        quant_class = other.__class__
        assert (
            quant_class == Forall or quant_class == Exists
        ), f"{other} is not a quantified proposition"
        assert isinstance(
            other.inner_proposition, Implies
        ), f"{other.inner_proposition} is not an implication"
        assert self.is_proven, f"{self} is not proven"
        assert other.is_proven, f"{other} is not proven"

        other_cons = other.inner_proposition.consequent.copy()
        new_p: Forall[B] | Exists[B] = quant_class(
            variable=other.variable.copy(),
            inner_proposition=other_cons,  # type: ignore
            is_assumption=False,
            _is_proven=True,
        )
        return new_p
