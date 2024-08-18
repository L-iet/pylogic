from __future__ import annotations
from pylogic.proposition.relation.binaryrelation import BinaryRelation
from pylogic.inference import Inference
from typing import TYPE_CHECKING, TypedDict
from pylogic.expressions.expr import evaluate

if TYPE_CHECKING:
    from fractions import Fraction
    from pylogic.symbol import Symbol
    from pylogic.structures.set_ import Set
    from pylogic.expressions.expr import Expr
    import sympy as sp

    Numeric = Fraction | int | float
    PBasic = Symbol | Numeric
    Unevaluated = Symbol | Set | Expr
    Term = Unevaluated | Numeric | sp.Basic
import copy

Tactic = TypedDict("Tactic", {"name": str, "arguments": list[str]})


class IsContainedIn(BinaryRelation):
    is_transitive = False
    name = "IsContainedIn"
    infix_symbol = "in"
    infix_symbol_latex = r"\in"
    tactics: list[Tactic] = [
        {"name": "by_containment_func", "arguments": []},
        {"name": "by_def", "arguments": []},
    ]

    def __init__(
        self,
        left: Term,
        right: Set,
        is_assumption: bool = False,
        description: str = "",
        **kwargs,
    ) -> None:
        self.right: Set = right
        self.left: Term = left
        name = "IsContainedIn"
        super().__init__(
            left,
            right,
            is_assumption=is_assumption,
            description=description,
            **kwargs,
        )

    @property
    def set_(self) -> Set:
        return self.right

    @property
    def element(self) -> Term:
        return self.left

    def by_containment_func(self) -> IsContainedIn:
        """Logical tactic. Use the set's containment function to prove that it
        contains the element
        """
        try:
            if self.right.containment_function(self.left):
                return IsContainedIn(
                    copy.copy(self.element),
                    self.set_.copy(),
                    _is_proven=True,
                    _assumptions=set(),
                    _inference=Inference(self, rule="by_containment_func"),
                )
        except Exception as e:
            raise ValueError(
                f"Cannot prove that {self.right} contains {self.left}\nThis was a result of\n{e}"
            )
        else:
            raise ValueError(f"Cannot prove that {self.right} contains {self.left}")

    def by_def(self) -> IsContainedIn:
        """Logical tactic. Use sympy's definition of the set to prove that
        it contains the element.
        """
        try:
            if (
                self.left in self.right.elements
                or evaluate(self.left) in self.right.sympy_set
            ):
                return IsContainedIn(
                    copy.copy(self.element),
                    self.set_.copy(),
                    is_assumption=self.is_assumption,
                    _is_proven=True,
                    _assumptions=set(),
                    _inference=Inference(self, rule="by_def"),
                )
        except (TypeError, NotImplementedError) as e:
            raise ValueError(
                f"Cannot prove that {self.right} contains {self.left}\nThis was a result of\n{e}"
            )
        raise ValueError(f"Cannot prove that {self.right} contains {self.left}")

    def by_inspection(self) -> IsContainedIn:
        """Logical tactic. Use the set's containment function and sympy set to
        prove that it contains the element.
        """
        try:
            return self.by_containment_func()
        except ValueError:
            return self.by_def()
