from __future__ import annotations
from pylogic.proposition.relation.binaryrelation import BinaryRelation
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from sympy import Basic

    SympyExpression = Basic | int | float
    from pylogic.set.sets import Set
import copy


class Contains(BinaryRelation):
    is_transitive = False
    name = "Contains"
    infix_symbol = "in"
    infix_symbol_latex = r"\in"

    def __init__(
        self,
        right: Set,
        left: SympyExpression | Set,
        is_assumption: bool = False,
        show_arg_position_names: bool = False,
        _is_proven: bool = False,
    ) -> None:
        self.right: Set = right
        self.left: SympyExpression | Set = left
        name = rf"Contains"
        super().__init__(
            left, right, is_assumption=is_assumption, _is_proven=_is_proven
        )

    @property
    def set_(self) -> Set:
        return self.right

    @property
    def element(self) -> SympyExpression | Set:
        return self.left

    def copy(self) -> "Contains":
        return Contains(
            self.set_.copy(),
            copy.copy(self.element),
            is_assumption=self.is_assumption,
            _is_proven=self.is_proven,
        )
