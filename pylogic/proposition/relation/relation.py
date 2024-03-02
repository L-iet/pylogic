from __future__ import annotations
from pylogic.proposition.proposition import Proposition
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from sympy import Basic as SympyExpression
    from pylogic.set.sets import Set
from sympy.printing.latex import LatexPrinter

latex_printer = LatexPrinter()


class Relation(Proposition):
    def __init__(
        self,
        name: str,
        completed_args: dict[str, Set | SympyExpression],
        is_assumption: bool = False,
        show_arg_position_names: bool = False,
        _is_proven: bool = False,
    ) -> None:
        assert len(completed_args) > 1, "Relation must have at least two arguments"
        super().__init__(
            name,
            is_assumption,
            completed_args=completed_args,
            show_arg_position_names=show_arg_position_names,
            _is_proven=_is_proven,
        )

    def __repr__(self) -> str:
        return super().__repr__()

    def _latex(self, printer=latex_printer) -> str:
        return super()._latex()

    def copy(self) -> "Relation":
        return Relation(
            self.name,
            completed_args=self.completed_args.copy(),
            is_assumption=self.is_assumption,
            show_arg_position_names=self.show_arg_position_names,
            _is_proven=self.is_proven,
        )
