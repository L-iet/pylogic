from __future__ import annotations
from pylogic.proposition.relation.binaryrelation import BinaryRelation
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from sympy import Basic

    SympyExpression = Basic | int | float
    from pylogic.set.sets import Set
import copy


class IsContainedIn(BinaryRelation):
    is_transitive = False
    name = "IsContainedIn"
    infix_symbol = "in"
    infix_symbol_latex = r"\in"

    def __init__(
        self,
        left: SympyExpression | Set,
        right: Set,
        is_assumption: bool = False,
        show_arg_position_names: bool = False,
        _is_proven: bool = False,
    ) -> None:
        self.right: Set = right
        self.left: SympyExpression | Set = left
        name = rf"IsContainedIn"
        super().__init__(
            left, right, is_assumption=is_assumption, _is_proven=_is_proven
        )

    @property
    def set_(self) -> Set:
        return self.right

    @property
    def element(self) -> SympyExpression | Set:
        return self.left

    def copy(self) -> "IsContainedIn":
        return IsContainedIn(
            copy.copy(self.element),
            self.set_.copy(),
            is_assumption=self.is_assumption,
            _is_proven=self.is_proven,
        )

    def by_containment_func(self) -> IsContainedIn:
        """Logical tactic. Use the set's containment function to prove that it
        contains the element
        """
        if self.right.containment_function(self.left):
            return IsContainedIn(
                copy.copy(self.element),
                self.set_.copy(),
                is_assumption=self.is_assumption,
                _is_proven=True,
            )
        raise ValueError(f"Cannot prove that {self.right} contains {self.left}")

    def by_def(self) -> IsContainedIn:
        """Logical tactic. Use sympy's definition of the set to prove that
        it contains the element.
        """
        try:
            if self.left in self.right.sympy_set:
                return IsContainedIn(
                    copy.copy(self.element),
                    self.set_.copy(),
                    is_assumption=self.is_assumption,
                    _is_proven=True,
                )
        except (TypeError, NotImplementedError) as e:
            raise ValueError(
                f"Cannot prove that {self.right} contains {self.left}\nThis was a result of\n{e}"
            )
        raise ValueError(f"Cannot prove that {self.right} contains {self.left}")
