from __future__ import annotations
from pylogic.proposition.proposition import Proposition
from typing import TYPE_CHECKING, Self

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
        description: str = "",
        _is_proven: bool = False,
    ) -> None:
        super().__init__(
            name,
            is_assumption,
            description=description,
            args=args,
            _is_proven=_is_proven,
        )
        self.is_atomic = True

    def __repr__(self) -> str:
        return super().__repr__()

    def as_text(self, *, _indent=0) -> str:
        """
        Return a text representation of the proposition.
        """
        return "  " * _indent + repr(self) + "\n"

    def _latex(self, printer=latex_printer) -> str:
        return super()._latex()

    def copy(self) -> Self:
        return self.__class__(
            self.name,
            args=self.args.copy(),
            is_assumption=self.is_assumption,
            description=self.description,
            _is_proven=self.is_proven,
        )
