from __future__ import annotations
from pylogic.proposition.proposition import Proposition
from typing import TYPE_CHECKING, Self, TypeVar, Generic
from abc import ABC, abstractmethod

from sympy import Basic, latex

if TYPE_CHECKING:
    from pylogic.set.sets import Set
    from pylogic.variable import Variable
    from pylogic.symbol import Symbol

    Term = Variable | Symbol | Set | Basic | int | float
from sympy.printing.latex import LatexPrinter

latex_printer = LatexPrinter()

TProposition = TypeVar("TProposition", bound="Proposition")


class _Quantified(Proposition, Generic[TProposition], ABC):
    def __init__(
        self,
        _q: str,
        variable: Variable,
        inner_proposition: TProposition,
        is_assumption: bool = False,
        _is_proven: bool = False,
    ) -> None:
        assert variable is not None, f"{self} must have a variable to quantify over"
        super().__init__(
            f"{_q} {variable}: {inner_proposition.name}",
            is_assumption,
            args=inner_proposition.args,
            _is_proven=_is_proven,
        )
        self.inner_proposition: TProposition = inner_proposition
        self.variable: Variable = variable
        self._q = _q
        self.is_atomic = False

    def __repr__(self) -> str:
        return f"{self._q} {self.variable}: {self.inner_proposition}"

    @abstractmethod
    def copy(self) -> Self:
        pass

    def replace(
        self,
        current_val: Term,
        new_val: Term,
        positions: list[list[int]] | None = None,
    ) -> Self:
        # assert not isinstance(new_val, Var), f"{new_val} is a Var"
        new_p: Self = self.copy()
        new_p.inner_proposition = new_p.inner_proposition.replace(
            current_val, new_val, positions
        )
        new_p._is_proven = False
        return new_p

    def _latex(self, printer=latex_printer) -> str:
        q_arg = self.variable
        arg_latex = q_arg._latex() if hasattr(q_arg, "_latex") else latex(q_arg)  # type: ignore
        return rf"\{self._q} {arg_latex}: {self.inner_proposition._latex()}"
