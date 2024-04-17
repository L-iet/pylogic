from __future__ import annotations
from pylogic.proposition.proposition import Proposition
from typing import TYPE_CHECKING, TypeVar, Generic, Self, overload

from pylogic.set.sets import Set

if TYPE_CHECKING:
    import sympy as sp
    from pylogic.proposition.implies import Implies

TProposition = TypeVar("TProposition", bound="Proposition")
UProposition = TypeVar("UProposition", bound="Proposition")


@overload
def neg(p: TProposition, is_assumption: bool = False) -> Not[TProposition]: ...


@overload
def neg(p: Not[TProposition], is_assumption: bool = False) -> TProposition: ...


def neg(
    p: TProposition | Not[TProposition], is_assumption: bool = False
) -> Not[TProposition] | TProposition:
    if isinstance(p, Not):
        return p.negated
    return Not(p, is_assumption)


def are_negs(p: Proposition, q: Proposition) -> bool:
    """Given two propositions, determine if they are negations
    of each other.
    """
    if isinstance(p, Not):
        return p.negated == q
    elif isinstance(q, Not):
        return q.negated == p
    return False


class Not(Proposition, Generic[TProposition]):
    def __init__(
        self,
        negated: TProposition,
        is_assumption: bool = False,
        _is_proven: bool = False,
    ) -> None:
        self.negated: TProposition = negated
        name = rf"~{negated}"
        super().__init__(name, is_assumption, _is_proven=_is_proven)
        self.is_atomic = False

    def __eq__(self, other: Proposition) -> bool:
        if isinstance(other, Not):
            return other.negated == self.negated
        return False

    def copy(self) -> Self:
        return self.__class__(
            self.negated.copy(), self.is_assumption, _is_proven=self.is_proven
        )

    def replace(
        self,
        current_val: sp.Basic | int | float,
        new_val: sp.Basic | int | float,
        positions: list[list[int]] | None = None,
    ) -> Self:
        new_p = self.copy()
        new_p.negated = new_p.negated.replace(current_val, new_val, positions=positions)
        new_p.name = rf"~{new_p.negated}"
        return new_p

    @overload
    def modus_tollens(
        self,
        other: Implies[Not[UProposition], TProposition],
    ) -> UProposition: ...

    @overload
    def modus_tollens(
        self,
        other: Implies[UProposition, TProposition],
    ) -> Not[UProposition]: ...

    def modus_tollens(
        self,
        other: (
            Implies[Not[UProposition], TProposition]
            | Implies[UProposition, TProposition]
        ),
    ) -> UProposition | Not[UProposition]:
        """
        Logical tactic.
        other: Implies
            Must be an implication that has been proven whose structure is
            OtherProposition -> ~self
        """
        return super().modus_tollens(other)  # type: ignore
