from __future__ import annotations
from pylogic.proposition.proposition import Proposition
from typing import TYPE_CHECKING, Self

if TYPE_CHECKING:
    from sympy import Basic as SympyExpression
    from pylogic.set.sets import Set
from sympy.printing.latex import LatexPrinter
import sympy as sp

latex_printer = LatexPrinter()


class _Quantified(Proposition):
    def __init__(
        self,
        _q: str,
        inner_proposition: Proposition,
        is_assumption: bool = False,
        quantified_arg: tuple[str, Set | SympyExpression] | None = None,
        show_arg_position_names: bool = False,
        _is_proven: bool = False,
    ) -> None:
        assert quantified_arg is not None, f"{self} must have a quantified arg"
        super().__init__(
            f"{_q} {quantified_arg[1]}: {inner_proposition.name}",
            is_assumption,
            completed_args=inner_proposition.completed_args,
            completed_args_order=inner_proposition.completed_args_order,
            show_arg_position_names=show_arg_position_names,
            _is_proven=_is_proven,
        )
        self.inner_proposition = inner_proposition
        self.quantified_arg = quantified_arg
        self._q = _q

    def __repr__(self) -> str:
        return f"{self._q} {self.quantified_arg[1]}: {self.inner_proposition}"

    @classmethod
    def copy(cls, instance) -> Self:
        return cls(
            instance.inner_proposition.copy(),
            instance.is_assumption,
            instance.quantified_arg,
            instance.show_arg_position_names,
            instance.is_proven,
        )

    def replace(
        self,
        current_val: Set | SympyExpression,
        new_val: Set | SympyExpression,
        positions: list[list[int]] | None = None,
    ) -> Self:
        new_p = self.copy()
        new_p.inner_proposition = new_p.inner_proposition.replace(
            current_val, new_val, positions
        )
        if new_p.quantified_arg[1] == current_val:
            new_p.quantified_arg = (new_p.quantified_arg[0], new_val)
        new_p._is_proven = False
        return new_p

    def _latex(self, printer=latex_printer) -> str:
        q_arg = self.quantified_arg[1]
        arg_latex = q_arg._latex() if hasattr(q_arg, "_latex") else sp.latex(q_arg)
        return rf"\{self._q} {arg_latex}: {self.inner_proposition._latex()}"
