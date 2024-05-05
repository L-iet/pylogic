from __future__ import annotations
from pylogic.printing.printing import str_print_order, latex_print_order
from pylogic.proposition.proposition import get_assumptions
from pylogic.proposition.relation.relation import Relation
from typing import TYPE_CHECKING, Self
from sympy import Basic, latex

if TYPE_CHECKING:
    from pylogic.structures.sets import Set
    from pylogic.symbol import Symbol

    Term = Symbol | Set | Basic | int | float


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
        description: str = "",
        **kwargs,
    ) -> None:
        super().__init__(
            self.name,
            args=[left, right],
            is_assumption=is_assumption,
            description=description,
            **kwargs,
        )
        self.left: Term = left
        self.right: Term = right

    def __repr__(self) -> str:
        return f"{str_print_order(self.left)} {self.infix_symbol} {str_print_order(self.right)}"

    def _latex(self, printer=None) -> str:
        left_latex = latex_print_order(self.left)
        right_latex = latex_print_order(self.right)
        return f"{left_latex} {self.infix_symbol_latex} {right_latex}"

    def copy(self) -> Self:
        # copy.copy and deepcopy are evaluating unevaluated expressions
        return self.__class__(
            self.left,
            self.right,
            description=self.description,
            is_assumption=self.is_assumption,
            _is_proven=self._is_proven,
            _assumptions=self.from_assumptions,
            _inference=self.deduced_from,
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
            _is_proven=False,
        )

    def transitive(self, other: Self) -> Self:
        """Logical Tactic. If self is of the form a Relation b and other is of the form b Relation c,
        returns a proven relation of the form a Relation c.
        """
        from pylogic.inference import Inference

        assert self.__class__.is_transitive, f"{self.__class__} is not transitive"
        assert self.is_proven, f"{self} is not proven"
        assert other.is_proven, f"{other} is not proven"
        assert isinstance(other, self.__class__), f"{other} is not a {self.__class__}"
        assert (
            self.right == other.left
        ), f"{self} and {other} do not fulfill transitivity"
        new_p = self.__class__(
            self.left,
            other.right,
            _is_proven=True,
            _assumptions=get_assumptions(self).union(get_assumptions(other)),
            _inference=Inference(self, other, rule="transitive"),
        )
        return new_p
