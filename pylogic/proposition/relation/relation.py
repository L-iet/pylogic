from __future__ import annotations
from pylogic.proposition.proposition import Proposition
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from pylogic.structures.sets import Set
    from pylogic.symbol import Symbol
    from sympy import Basic

    Term = Symbol | Set | Basic | int | float
from sympy.printing.latex import LatexPrinter

latex_printer = LatexPrinter()


class Relation(Proposition):
    def __init__(
        self,
        name: str,
        args: list[Term],
        is_assumption: bool = False,
        _is_proven: bool = False,
    ) -> None:
        super().__init__(
            name,
            is_assumption,
            args=args,
            _is_proven=_is_proven,
        )
        self.is_atomic = True

    def __repr__(self) -> str:
        return super().__repr__()

    def _latex(self, printer=latex_printer) -> str:
        return super()._latex()

    def copy(self) -> Relation:
        return Relation(
            self.name,
            args=self.args.copy(),
            is_assumption=self.is_assumption,
            _is_proven=self.is_proven,
        )
