from __future__ import annotations
from typing import TYPE_CHECKING, Self, TypeVar, TypedDict

from pylogic.proposition.proposition import Proposition, get_assumptions
from pylogic.proposition.quantified.quantified import _Quantified
from pylogic.proposition.relation.contains import IsContainedIn
from pylogic.proposition.implies import Implies
from pylogic.inference import Inference

import sympy as sp


if TYPE_CHECKING:
    from pylogic.proposition.relation.equals import Equals
    from pylogic.proposition.not_ import Not
    from pylogic.variable import Variable
    from pylogic.proposition.quantified.exists import Exists
    from pylogic.proposition.relation.contains import IsContainedIn
    from pylogic.symbol import Symbol
    from pylogic.structures.sets import Set
    from pylogic.expressions.expr import Expr

    Term = Symbol | Set | Expr | int | float


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
        description: str = "",
        **kwargs,
    ) -> None:
        super().__init__(
            "forall",
            variable,
            inner_proposition,
            is_assumption,
            description=description,
            **kwargs,
        )

    def __eq__(self, other: Proposition) -> bool:
        if isinstance(other, Forall):
            return self.inner_proposition == other.inner_proposition
        return False

    def __hash__(self) -> int:
        return super().__hash__()

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
        MatEl = sp.matrices.expressions.matexpr.MatrixElement  # type: ignore
        assert isinstance(prop.left, MatEl) and isinstance(
            prop.right, MatEl
        ), f"The inner equality {prop} is not between matrix elements"
        left_mat, *left_indices = prop.left.args  # type: ignore
        right_mat, *right_indices = prop.right.args  # type: ignore
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
            _assumptions=get_assumptions(self).union(get_assumptions(other)),
            _inference=Inference(self, other, rule="quantified_modus_ponens"),
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
        new_p = self.__class__(
            self.variable,
            self.inner_proposition.replace(current_val, new_val, positions=positions),
            _is_proven=False,
        )
        return new_p

    def in_particular(self, expression_to_substitute: Term) -> TProposition:
        """Logical tactic. Given self is proven, replace the variable in the inner
        proposition and get a proven proposition.
        """
        # TODO: may need to define or override .replace for Forall to prevent
        # unnecessarily replacing the variable in the inner proposition
        assert self.is_proven, f"{self} is not proven"
        # I previously checked that expression_to_substitute does
        # not contain variables, but I think it's not necessary
        new_p = self.inner_proposition.replace(self.variable, expression_to_substitute)
        new_p._is_proven = True
        new_p.from_assumptions = get_assumptions(self).copy()
        new_p.deduced_from = Inference(self, rule="in_particular")
        return new_p

    def de_morgan(self) -> Not[Exists[Not[TProposition]]]:
        """
        Apply De Morgan's law to a universally quantified sentence.
        """
        from pylogic.proposition.not_ import Not, neg
        from pylogic.proposition.quantified.exists import Exists

        inner_negated = neg(self.inner_proposition.de_morgan())
        self.variable.unbind()
        return Not(
            Exists(self.variable, inner_negated),
            _is_proven=self.is_proven,
            _assumptions=get_assumptions(self).copy(),
            _inference=Inference(self, rule="de_morgan"),
        )


class ForallInSet(Forall[Implies[IsContainedIn, TProposition]]):
    def __init__(
        self,
        variable: Variable,
        set_: Set,
        inner_proposition: TProposition,
        is_assumption: bool = False,
        description: str = "",
        **kwargs,
    ) -> None:
        super().__init__(
            variable,
            IsContainedIn(variable, set_).implies(inner_proposition),
            is_assumption,
            description=description,
            **kwargs,
        )
        self.set_ = set_
        self._inner_without_set = inner_proposition

    def __hash__(self) -> int:
        return super().__hash__()

    def __repr__(self) -> str:
        return f"forall {self.variable} in {self.set_}: {self._inner_without_set}"

    def replace(
        self,
        current_val: Term,
        new_val: Term,
        positions: list[list[int]] | None = None,
    ) -> Self:
        if current_val == self.variable:
            raise ValueError("Cannot replace variable (not implemented)")
        if current_val == self.set_:
            assert isinstance(new_val, Set), f"{new_val} is not a set"
            new_p = self.__class__(
                self.variable,
                new_val,
                self._inner_without_set.replace(
                    current_val, new_val, positions=positions
                ),
                _is_proven=False,
            )

        new_p = self.__class__(
            self.variable,
            self.set_,
            self._inner_without_set.replace(current_val, new_val, positions=positions),
            _is_proven=False,
        )
        return new_p

    def to_forall(self) -> Forall[Implies[IsContainedIn, TProposition]]:
        """
        Convert self to a regular `forall` statement.
        """
        return Forall(
            self.variable,
            self.inner_proposition,
            is_assumption=self.is_assumption,
            description=self.description,
            _is_proven=self._is_proven,
            _assumptions=self.from_assumptions,
            _inference=self.deduced_from,
        )

    def in_particular(self, expression_to_substitute: Term) -> TProposition:
        """Logical tactic. Given self is proven, replace the variable in the inner
        proposition and get a proven proposition.
        """
        assert self.is_proven, f"{self} is not proven"
        impl = super().in_particular(expression_to_substitute)
        ante = IsContainedIn(expression_to_substitute, self.set_).by_inspection()
        if ante == impl.antecedent:
            new_p = impl.consequent
            new_p._is_proven = True
            new_p.from_assumptions = get_assumptions(self).copy()
            new_p.deduced_from = Inference(self, rule="in_particular")
            return new_p
        else:
            raise ValueError("Inconsistent substitution occured.")
