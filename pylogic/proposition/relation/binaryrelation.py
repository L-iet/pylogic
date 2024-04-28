from __future__ import annotations
from pylogic.proposition.relation.relation import Relation
from typing import TYPE_CHECKING, Self
from sympy import Basic, latex

if TYPE_CHECKING:
    from pylogic.structures.sets import Set
    from pylogic.variable import Variable
    from pylogic.symbol import Symbol

    Term = Variable | Symbol | Set | Basic | int | float

from sympy.printing.latex import LatexPrinter

latex_printer = LatexPrinter()


class BinaryRelation(Relation):
    is_transitive: bool = False
    name: str = "BR"
    infix_symbol: str = "BR"
    infix_symbol_latex: str = "BR"

    def __init__(
        self,
        left: Term,
        right: Term,
        is_assumption: bool = False,
        _is_proven: bool = False,
    ) -> None:
        super().__init__(
            self.name,
            args=[left, right],
            is_assumption=is_assumption,
            _is_proven=_is_proven,
        )
        self.left: Term = left
        self.right: Term = right

    def __repr__(self) -> str:
        return f"{self.left} {self.infix_symbol} {self.right}"

    def _latex(self, printer=latex_printer) -> str:
        left_ = self.left
        left_latex = left_._latex() if hasattr(left_, "_latex") else latex(left_)
        right_ = self.right
        right_latex = right_._latex() if hasattr(right_, "_latex") else latex(right_)
        return f"{left_latex} {self.infix_symbol_latex} {right_latex}"

    def copy(self) -> Self:
        # copy.copy and deepcopy are evaluating unevaluated expressions
        return self.__class__(
            self.left,  # was copy.copy(self.left), same for right
            self.right,
            is_assumption=self.is_assumption,
            _is_proven=self.is_proven,
        )

    def replace(
        self,
        current_val: Term,
        new_val: Term,
        positions: list[list[int]] | None = None,
    ) -> Self:
        new_p = self.copy()

        if positions is None or [0] in positions:
            if isinstance(new_p.left, Basic):
                new_p.left = new_p.left.subs(current_val, new_val)
            elif new_p.left == current_val:
                new_p.left = new_val
        if positions is None or [1] in positions:
            if isinstance(new_p.right, Basic):
                new_p.right = new_p.right.subs(current_val, new_val)
            elif new_p.right == current_val:
                new_p.right = new_val
        return self.__class__(
            new_p.left,
            new_p.right,
            is_assumption=self.is_assumption,
            _is_proven=False,
        )

    def transitive(self, other: Self) -> Self:
        """Logical Tactic. If self is of the form a Relation b and other is of the form b Relation c,
        returns a proven relation of the form a Relation c.
        """
        assert self.__class__.is_transitive, f"{self.__class__} is not transitive"
        assert self.is_proven, f"{self} is not proven"
        assert other.is_proven, f"{other} is not proven"
        assert isinstance(other, self.__class__), f"{other} is not a {self.__class__}"
        assert (
            self.right == other.left
        ), f"{self} and {other} do not fulfill transitivity"
        new_p = self.__class__(self.left, other.right)
        new_p._is_proven = True
        return new_p
