from __future__ import annotations
from pylogic.proposition.proposition import Proposition
from pylogic.proposition.not_ import neg
from typing import TYPE_CHECKING, TypeVar, Generic, TypedDict

if TYPE_CHECKING:
    from sympy import Basic as SympyExpression
    from pylogic.proposition.or_ import Or
    from pylogic.set.sets import Set
from sympy.printing.latex import LatexPrinter

latex_printer = LatexPrinter()

TProposition = TypeVar("TProposition", bound="Proposition")
UProposition = TypeVar("UProposition", bound="Proposition")
VProposition = TypeVar("VProposition", bound="Proposition")
Tactic = TypedDict("Tactic", {"name": str, "arguments": list[str]})


class Implies(Proposition, Generic[TProposition, UProposition]):
    tactics: list[Tactic] = [
        {"name": "hypothetical_syllogism", "arguments": ["Implies"]}
    ]

    # TODO: Implement __eq__ for Implies, And, Or, IsContainedIn, Relation, Equals etc
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
        self.completed_args = getattr(self.antecedent, "completed_args", {}).copy()
        self.completed_args.update(getattr(self.consequent, "completed_args", {}))
        self.completed_args_order = getattr(
            self.antecedent, "completed_args_order", []
        ).copy()
        self.completed_args_order.extend(
            getattr(self.consequent, "completed_args_order", [])
        )
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
        current_val: Set | SympyExpression,
        new_val: Set | SympyExpression,
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
