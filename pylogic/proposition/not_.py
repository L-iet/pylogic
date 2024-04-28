from __future__ import annotations
from pylogic.proposition.proposition import Proposition
from typing import TYPE_CHECKING, Literal, TypeVar, Generic, Self, overload, TypedDict
from sympy.printing.latex import LatexPrinter

latex_printer = LatexPrinter()

if TYPE_CHECKING:
    from pylogic.proposition.implies import Implies
    from pylogic.variable import Variable
    from pylogic.symbol import Symbol
    from pylogic.set.sets import Set
    from sympy import Basic

    Term = Variable | Symbol | Set | Basic | int | float
    Unification = dict[Variable, Term]

TProposition = TypeVar("TProposition", bound="Proposition")
UProposition = TypeVar("UProposition", bound="Proposition")
Tactic = TypedDict("Tactic", {"name": str, "arguments": list[str]})


@overload
def neg(
    p: Not[TProposition], is_assumption: bool = False, **kwargs
) -> TProposition: ...


@overload
def neg(
    p: TProposition, is_assumption: bool = False, **kwargs
) -> Not[TProposition]: ...


def neg(
    p: Not[TProposition] | TProposition, is_assumption: bool = False, **kwargs
) -> Not[TProposition] | TProposition:
    """
    Given a proposition, return its negation.
    """
    _is_proven = kwargs.get("_is_proven", False)
    if isinstance(p, Not):
        return p.negated
    return Not(p, is_assumption, _is_proven=_is_proven)


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
    tactics: list[Tactic] = [
        {"name": "modus_tollens", "arguments": ["Implies"]},
        {"name": "de_morgan", "arguments": []},
    ]

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

    def de_morgan(self) -> Proposition:
        """
        Apply De Morgan's law to this negation.
        """
        from pylogic.proposition.and_ import And
        from pylogic.proposition.or_ import Or

        if isinstance(self.negated, And):
            negs: list[Proposition] = [
                neg(p.de_morgan()) for p in self.negated.propositions  # type:ignore
            ]
            return Or(*negs, _is_proven=self.is_proven)  # type: ignore
        elif isinstance(self.negated, Or):
            negs: list[Proposition] = [
                neg(p.de_morgan()) for p in self.negated.propositions  # type:ignore
            ]
            return And(*negs, _is_proven=self.is_proven)  # type: ignore
        elif self.negated.is_atomic:
            return self.copy()

        return neg(self.negated.de_morgan(), _is_proven=self.is_proven)

    def unify(self, other: Self) -> Unification | Literal[True] | None:
        if not isinstance(other, Not):
            raise TypeError(
                f"{other} is not an instance of {self.__class__}\n\
Occured when trying to unify `{self}` and `{other}`"
            )
        return self.negated.unify(other.negated)
