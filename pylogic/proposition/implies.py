from __future__ import annotations
from pylogic.proposition.proposition import Proposition
from pylogic.proposition.not_ import neg
from typing import TYPE_CHECKING, Literal, TypeVar, Generic, TypedDict, Self

if TYPE_CHECKING:
    from pylogic.proposition.or_ import Or
    from pylogic.structures.sets import Set
    from pylogic.variable import Variable
    from pylogic.symbol import Symbol
    from sympy import Basic

    Term = Variable | Symbol | Set | Basic | int | float
    Unification = dict[Variable, Term]
from sympy.printing.latex import LatexPrinter

latex_printer = LatexPrinter()

TProposition = TypeVar("TProposition", bound="Proposition")
UProposition = TypeVar("UProposition", bound="Proposition")
VProposition = TypeVar("VProposition", bound="Proposition")
Tactic = TypedDict("Tactic", {"name": str, "arguments": list[str]})


class Implies(Proposition, Generic[TProposition, UProposition]):
    tactics: list[Tactic] = [
        {"name": "hypothetical_syllogism", "arguments": ["Implies"]},
        {"name": "impl_elim", "arguments": []},
        {"name": "definite_clause_resolve", "arguments": ["Proposition"]},
    ]

    # TODO: Implement __eq__ for IsContainedIn, Relation, Equals etc
    def __init__(
        self,
        antecedent: TProposition,
        consequent: UProposition,
        is_assumption: bool = False,
        _is_proven: bool = False,
    ) -> None:
        self.antecedent = antecedent
        self.consequent = consequent
        name = f"{antecedent.name} -> {consequent.name}"
        super().__init__(name, is_assumption, _is_proven=_is_proven)
        self.is_atomic = False

    def __eq__(self, other: Proposition) -> bool:
        if isinstance(other, Implies):
            return (
                self.antecedent == other.antecedent
                and self.consequent == other.consequent
            )
        return False

    def __hash__(self) -> int:
        return hash(("impl", self.antecedent, self.consequent))

    def __repr__(self) -> str:
        return f"[{self.antecedent} -> {self.consequent}]"

    def _latex(self, printer=latex_printer) -> str:
        return rf"\left({self.antecedent._latex()} \rightarrow {self.consequent._latex()}\right)"

    def copy(self) -> "Implies":
        return Implies(
            self.antecedent.copy(),
            self.consequent.copy(),
            self.is_assumption,
            _is_proven=self.is_proven,
        )

    def replace(
        self,
        current_val: Term,
        new_val: Term,
        positions: list[list[int]] | None = None,
    ) -> "Implies":
        if positions is not None:
            ante_positions = [p[1:] for p in positions if p[0] == 0]
            cons_positions = [p[1:] for p in positions if p[0] == 1]
            ante_positions = None if [] in ante_positions else ante_positions
            cons_positions = None if [] in cons_positions else cons_positions
        else:
            ante_positions = None
            cons_positions = None
        new_p = self.copy()
        new_p.antecedent = new_p.antecedent.replace(
            current_val, new_val, ante_positions
        )
        new_p.consequent = new_p.consequent.replace(
            current_val, new_val, cons_positions
        )
        new_p._is_proven = False
        return new_p

    def hypothetical_syllogism(
        self, other: Implies[UProposition, VProposition]
    ) -> Implies[TProposition, VProposition]:
        """
        Logical tactic.
        """
        assert self.is_proven, f"{self} is not proven"
        assert isinstance(other, Implies), f"{other} is not an implication"
        assert other.is_proven, f"{other} is not proven"
        assert (
            self.consequent == other.antecedent
        ), f"Does not follow logically: {self.name},  {other.name}"
        i = Implies(self.antecedent, other.consequent)
        i._is_proven = True
        return i

    def impl_elim(self) -> Or:
        r"""Logical tactic. Given self (A -> B) is proven, return the corresponding
        disjunction form (~A \/ B)
        """
        assert self.is_proven, f"{self} is not proven"
        return Or(neg(self.antecedent), self.consequent, _is_proven=True)

    def definite_clause_resolve(
        self, in_body: Proposition
    ) -> Self | Implies[Proposition, UProposition]:
        r"""
        Logical tactic. Given self (A /\ B /\ C...) -> D is proven, and
        given one of the props in the antecedent B is proven,
        return a proof of the new definite clause (A /\ C /\ ...) -> D
        or A -> D if only A is left in the body
        """
        from pylogic.proposition.and_ import And

        assert self.is_proven, f"{self} is not proven"
        assert in_body.is_proven, f"{in_body} is not proven"
        assert isinstance(
            self.antecedent, And
        ), f"The antecedent of {self} is not a conjunction"
        rem_props = [
            prop.copy() for prop in self.antecedent.propositions if prop != in_body
        ]
        if len(rem_props) == 1:
            return Implies(rem_props[0], self.consequent, _is_proven=True)
        new_p = Implies(And(*rem_props), self.consequent, _is_proven=True)
        return new_p  # type:ignore

    def unify(self, other: Self) -> Unification | Literal[True] | None:
        if not isinstance(other, Implies):
            raise TypeError(
                f"{other} is not an instance of {self.__class__}\n\
Occured when trying to unify `{self}` and `{other}`"
            )
        d: Unification = {}
        res1 = self.antecedent.unify(other.antecedent)
        if res1 is None:
            return None
        if isinstance(res1, dict):
            for k in res1:
                if k in d and d[k] != res1[k]:
                    return None
                d[k] = res1[k]
        res2 = self.consequent.unify(other.consequent)
        if res2 is None:
            return None
        if isinstance(res2, dict):
            for k in res2:
                if k in d and d[k] != res2[k]:
                    return None
                d[k] = res2[k]
        if len(d) == 0:
            return True
        else:
            return d
