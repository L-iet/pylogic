from __future__ import annotations
from pylogic.proposition.proposition import Proposition
from typing import TYPE_CHECKING, TypeVar, Generic

TProposition = TypeVar("TProposition", bound="Proposition")


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
        name = rf"~{negated.name}"
        super().__init__(name, is_assumption, _is_proven=_is_proven)
        self.is_atomic = False

    def __eq__(self, other: Proposition) -> bool:
        if isinstance(other, Not):
            return other.negated == self.negated
        return False

    def copy(self) -> "Not":
        return Not(self.negated.copy(), self.is_assumption, _is_proven=self.is_proven)
