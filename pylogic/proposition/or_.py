from __future__ import annotations
from pylogic.proposition.proposition import Proposition
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from sympy import Basic as SympyExpression
    from pylogic.set.sets import Set
from sympy.printing.latex import LatexPrinter

latex_printer = LatexPrinter()


class Or(Proposition):
    def __init__(
        self,
        *propositions: Proposition,
        is_assumption: bool = False,
    ) -> None:
        assert len(propositions) > 1, "'Or' must have at least two propositions"
        self.propositions = propositions
        name = r" \/ ".join([p.name for p in propositions])
        super().__init__(name, is_assumption)

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
