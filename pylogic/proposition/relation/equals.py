from __future__ import annotations
from pylogic.proposition.relation.binaryrelation import BinaryRelation
from pylogic.proposition.proposition import Proposition
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from sympy import Basic as SympyExpression
    from pylogic.set.sets import Set
from sympy.printing.latex import LatexPrinter
import sympy as sp

latex_printer = LatexPrinter()


class Equals(BinaryRelation):
    is_transitive = True
    name = "Equals"
    infix_symbol = "="
    infix_symbol_latex = "="

    def __init__(
        self,
        left: Set | SympyExpression,
        right: Set | SympyExpression,
        is_assumption: bool = False,
        _is_proven: bool = False,
    ) -> None:
        super().__init__(
            left,
            right,
            is_assumption=is_assumption,
            _is_proven=_is_proven,
        )
        self.left: Set | SympyExpression = left
        self.right: Set | SympyExpression = right
        self.left_doit = (
            self.left.doit() if isinstance(self.left, sp.Basic) else self.left
        )
        self.right_doit = (
            self.right.doit() if isinstance(self.right, sp.Basic) else self.right
        )
        self.doit_args = {"left": self.left_doit, "right": self.right_doit}

    def _check_provable_by_simplification(self, _checking_side: str) -> bool:
        """
        To check if we can use sympy methods to simplify and prove this equality.
        Parameters
        ----------
        _checking_side: str
            "left" or "right"
        tried_doit: bool
            Whether we have tried using doit() on the arguments.
        """
        other_side = "right" if _checking_side == "left" else "left"
        proven = False
        if self.left == self.right:
            proven = True
        elif isinstance(self.completed_args[_checking_side], sp.Basic):
            try:
                if self.completed_args[_checking_side].equals(
                    self.completed_args[other_side]
                ):
                    proven = True
            except ValueError:
                if self.doit_args[_checking_side] == self.doit_args[other_side]:
                    proven = True

        if not proven and not (
            isinstance(self.completed_args[_checking_side], int)
            or isinstance(self.completed_args[_checking_side], float)
        ):
            if self.doit_args[_checking_side].dummy_eq(self.doit_args[other_side]):
                proven = True
        return proven

    def by_simplification(self):
        """Logical tactic."""

        proven = self._check_provable_by_simplification("left")
        if not proven:
            proven = self._check_provable_by_simplification("right")
        if proven:
            new_p = self.copy()
            new_p._is_proven = True
            return new_p
        else:
            raise ValueError(f"{self} cannot be proven by simplification")

    def substitute_into(self, side: str, other_prop: Proposition) -> Proposition:
        """
        If side == "left", will look for self.right in other_prop and replace it with self.left.
        Parameters
        ----------
        side: str
            "left" or "right"
        other_prop: Proposition
            Proposition to search for the other side in.
        """
        if side not in ["left", "right"]:
            raise ValueError(f"Invalid side: {side}")
        other_side = "right" if side == "left" else "left"
        new_prop = other_prop.replace(
            self.completed_args[other_side], self.completed_args[side]
        )
        new_prop._is_proven = False
        return new_prop

    def p_substitute_into(self, side: str, other_prop: Proposition) -> Proposition:
        """
        Logical tactic.
        If side == "left", will look for self.right in other_prop and replace it with self.left.
        Returns a proven proposition.
        Parameters
        ----------
        side: str
            "left" or "right"
        other_prop: Proposition
            Proposition to search for the other side in.
        """
        assert self.is_proven, f"{self} is not proven"
        assert other_prop.is_proven, f"{other_prop} is not proven"
        new_prop = self.substitute_into(side, other_prop)
        new_prop._is_proven = True
        return new_prop
