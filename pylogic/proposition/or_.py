from __future__ import annotations
from pylogic.proposition.proposition import Proposition
from pylogic.proposition.not_ import are_negs
from typing import TYPE_CHECKING, TypeVar, TypedDict

if TYPE_CHECKING:
    from sympy import Basic as SympyExpression
    from pylogic.set.sets import Set
from sympy.printing.latex import LatexPrinter

latex_printer = LatexPrinter()
TProposition = TypeVar("TProposition", bound="Proposition")
Tactic = TypedDict("Tactic", {"name": str, "arguments": list[str]})


class Or(Proposition):
    tactics: list[Tactic] = [{"name": "unit_resolve", "arguments": ["Proposition"]}]

    def __init__(
        self,
        *propositions: Proposition,
        is_assumption: bool = False,
        _is_proven: bool = False,
    ) -> None:
        assert len(propositions) > 1, "'Or' must have at least two propositions"
        self.propositions = propositions
        name = r" \/ ".join([p.name for p in propositions])
        super().__init__(name, is_assumption, _is_proven=_is_proven)
        self.is_atomic = False

    def __eq__(self, other: Proposition) -> bool:
        if isinstance(other, Or):
            return self.propositions == other.propositions
        return False

    def copy(self) -> "Or":
        return Or(
            *[p.copy() for p in self.propositions], is_assumption=self.is_assumption
        )

    def replace(
        self,
        current_val: Set | SympyExpression,
        new_val: Set | SympyExpression,
        positions: list[list[int]] | None = None,
    ) -> "Or":
        if positions is not None:
            prop_positions_lists = [
                [p[1:] for p in positions if p[0] == i]
                for i in range(len(self.propositions))
            ]
            prop_positions_lists = list(
                map(lambda x: None if [] in x else x, prop_positions_lists)
            )
        else:
            prop_positions_lists = [None] * len(self.propositions)
        new_p = self.copy()
        new_p.propositions = [
            p.replace(current_val, new_val, prop_positions)
            for p, prop_positions in zip(new_p.propositions, prop_positions_lists)
        ]
        new_p._is_proven = False
        return new_p

    def __repr__(self) -> str:
        s = r" \/ ".join([p.__repr__() for p in self.propositions])
        return f"({s})"

    def _latex(self, printer=latex_printer) -> str:
        s = r"\vee ".join([p._latex() for p in self.propositions])
        return rf"\left({s}\right)"

    def unit_resolve(self, p: Proposition) -> Proposition | Or:
        """
        Logical tactic. Given self is proven, and p is proven, where p is
        a negation of one of the propositions in self, return a proven disjunction
        of the remaining propositions in self.
        """
        assert self.is_proven, f"{self} is not proven"
        assert p.is_proven, f"{p} is not proven"
        rem_props = [prop.copy() for prop in self.propositions if not are_negs(prop, p)]
        if len(rem_props) == 1:
            rem_props[0]._is_proven = True
            return rem_props[0]
        return Or(*rem_props, _is_proven=True)
