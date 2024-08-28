from __future__ import annotations

from typing import TYPE_CHECKING, Any, TypedDict, TypeVar

from pylogic.expressions.expr import to_sympy
from pylogic.inference import Inference
from pylogic.proposition.relation.binaryrelation import BinaryRelation

if TYPE_CHECKING:
    from fractions import Fraction

    from pylogic.expressions.expr import Expr
    from pylogic.proposition.proposition import Proposition
    from pylogic.structures.set_ import Set
    from pylogic.symbol import Symbol

    Numeric = Fraction | int | float
    PBasic = Symbol | Numeric
    Unevaluated = Symbol | Set | Expr
    Term = Unevaluated | Numeric
else:
    Set = Any
    Term = Any
T = TypeVar("T", bound=Term)
import copy

Tactic = TypedDict("Tactic", {"name": str, "arguments": list[str]})


class IsContainedIn(BinaryRelation[T, Set]):
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
        left: T,
        right: Set,
        is_assumption: bool = False,
        description: str = "",
        **kwargs,
    ) -> None:
        self.right: Set = right
        self.left: T = left
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

    def by_predicate(self, proven_predicate: Proposition) -> IsContainedIn:
        """Logical tactic. Use the set's predicate function to prove that it
        contains the element
        """
        if self.right.predicate is None:
            raise ValueError(f"{self.right} does not have a predicate function")
        try:
            if (
                proven_predicate.is_proven
                and self.right.predicate(self.left) == proven_predicate
            ):
                return IsContainedIn(
                    copy.copy(self.element),
                    self.set_.copy(),
                    _is_proven=True,
                    _assumptions=set(),
                    _inference=Inference(self, rule="by_predicate"),
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
                or to_sympy(self.left) in self.right.sympy_set  # type: ignore
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
