from __future__ import annotations
from pylogic.proposition.proposition import Proposition
from typing import TYPE_CHECKING, TypeVar, Generic, Self, overload
from sympy.printing.latex import LatexPrinter

latex_printer = LatexPrinter()

if TYPE_CHECKING:
    from pylogic.proposition.implies import Implies
    from pylogic.variable import Variable
    from pylogic.symbol import Symbol
    from pylogic.set.sets import Set
    from sympy import Basic

    Term = Variable | Symbol | Set | Basic | int | float

TProposition = TypeVar("TProposition", bound="Proposition")
UProposition = TypeVar("UProposition", bound="Proposition")


@overload
def neg(p: Not[TProposition], is_assumption: bool = False) -> TProposition: ...


@overload
def neg(p: TProposition, is_assumption: bool = False) -> Not[TProposition]: ...


def neg(
    p: Not[TProposition] | TProposition, is_assumption: bool = False
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

    def __hash__(self) -> int:
        return hash(("not", self.negated))

    def copy(self) -> Self:
        return self.__class__(
            self.negated.copy(), self.is_assumption, _is_proven=self.is_proven
        )

    def replace(
        self,
        current_val: Term,
        new_val: Term,
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

    def _latex(self, printer=latex_printer) -> str:
        return rf"\neg{{{self.negated._latex()}}}"
