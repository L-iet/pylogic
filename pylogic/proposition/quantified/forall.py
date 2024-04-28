from __future__ import annotations
from typing import TYPE_CHECKING, Self, TypeVar, TypedDict

from pylogic.proposition.proposition import Proposition
from pylogic.proposition.quantified.quantified import _Quantified
from pylogic.proposition.implies import Implies

import sympy as sp
from sympy.printing.latex import LatexPrinter


if TYPE_CHECKING:
    from pylogic.proposition.relation.equals import Equals
    from pylogic.proposition.not_ import Not
    from pylogic.variable import Variable
    from pylogic.proposition.quantified.exists import Exists
    from pylogic.symbol import Symbol
    from pylogic.structures.sets import Set

    Term = Variable | Symbol | Set | sp.Basic | int | float


TProposition = TypeVar("TProposition", bound="Proposition")
UProposition = TypeVar("UProposition", bound="Proposition")
B = TypeVar("B", bound="Proposition")
Tactic = TypedDict("Tactic", {"name": str, "arguments": list[str]})


class Forall(_Quantified[TProposition]):
    tactics: list[Tactic] = [
        {"name": "quantified_modus_ponens", "arguments": ["Implies"]},
        {"name": "hence_matrices_are_equal", "arguments": []},
        {"name": "de_morgan", "arguments": []},
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
            self.variable,
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
        assert self.inner_proposition == other.inner_proposition.antecedent

        other_cons = other.inner_proposition.consequent.copy()
        new_p: Forall[B] | Exists[B] = quant_class(
            variable=other.variable.copy(),
            inner_proposition=other_cons,  # type: ignore
            is_assumption=False,
            _is_proven=True,
        )
        return new_p

    def replace(
        self,
        current_val: Term,
        new_val: Term,
        positions: list[list[int]] | None = None,
    ) -> Self:
        if current_val == self.variable:
            raise ValueError("Cannot replace variable (not implemented)")
        new_p = self.copy()
        new_p.inner_proposition = new_p.inner_proposition.replace(
            current_val, new_val, positions=positions
        )
        return new_p

    def in_particular(self, expression_to_substitute: Term) -> TProposition:
        """Logical tactic. Given self is proven, replace the variable in the inner
        proposition and get a proven proposition.
        """
        # TODO: may need to define or override .replace for Forall to prevent
        # unnecessarily replacing the variable in the inner proposition
        assert self.is_proven, f"{self} is not proven"
        new_p = self.inner_proposition.replace(self.variable, expression_to_substitute)
        new_p._is_proven = True
        return new_p

    def de_morgan(self) -> Not[Exists[Not[TProposition]]]:
        """
        Apply De Morgan's law to a universally quantified sentence.
        """
        from pylogic.proposition.not_ import Not, neg
        from pylogic.proposition.quantified.exists import Exists

        inner_negated = neg(self.inner_proposition.de_morgan())
        return Not(Exists(self.variable, inner_negated), _is_proven=self.is_proven)
