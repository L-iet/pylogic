from __future__ import annotations
from pylogic.proposition.proposition import Proposition
from typing import TYPE_CHECKING, TypedDict

if TYPE_CHECKING:
    from sympy import Basic as SympyExpression
    from pylogic.set.sets import Set
from sympy.printing.latex import LatexPrinter

latex_printer = LatexPrinter()
Tactic = TypedDict("Tactic", {"name": str, "arguments": list[str]})


class And(Proposition):
    tactics: list[Tactic] = [{"name": "all_proven", "arguments": []}]

    def __init__(
        self,
        *propositions: Proposition,
        is_assumption: bool = False,
        _is_proven: bool = False,
    ) -> None:
        assert len(propositions) > 1, "'And' must have at least two propositions"
        self.propositions = propositions
        name = rf" /\ ".join([p.name for p in propositions])
        super().__init__(name, is_assumption, _is_proven=_is_proven)
        self.is_atomic = False

    def copy(self) -> "And":
        return And(
            *[p.copy() for p in self.propositions],
            is_assumption=self.is_assumption,
            _is_proven=self.is_proven,
        )

    def replace(
        self,
        current_val: Set | SympyExpression,
        new_val: Set | SympyExpression,
        positions: list[list[int]] | None = None,
    ) -> "And":
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
        s = r" /\ ".join([p.__repr__() for p in self.propositions])
        return f"({s})"

    def _latex(self, printer=latex_printer) -> str:
        s = r"\wedge ".join([p._latex() for p in self.propositions])
        return rf"\left({s}\right)"

    def all_proven(self) -> "And":
        """Logical tactic. If all propositions are proven, the conjunction is
        proven."""
        for p in self.propositions:
            if not p.is_proven:
                raise ValueError(f"{p} is not proven")
        new_p = self.copy()
        new_p._is_proven = True
        return new_p
