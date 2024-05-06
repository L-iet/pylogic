from __future__ import annotations
from pylogic.proposition.relation.binaryrelation import BinaryRelation
from pylogic.proposition.proposition import get_assumptions
from typing import TYPE_CHECKING, TypedDict, TypeVar, Self

if TYPE_CHECKING:
    from pylogic.proposition.proposition import Proposition
    from pylogic.symbol import Symbol
    from pylogic.structures.sets import Set
    from pylogic.proposition.relation.contains import IsContainedIn
    from pylogic.proposition.implies import Implies
    from pylogic.proposition.quantified.forall import Forall
    from pylogic.expressions.expr import Expr

    Term = Symbol | Set | Expr | int | float
TProposition = TypeVar("TProposition", bound="Proposition")
UProposition = TypeVar("UProposition", bound="Proposition")
Tactic = TypedDict("Tactic", {"name": str, "arguments": list[str]})


class Subset(BinaryRelation):
    is_transitive = True
    name = "IsSubsetOf"
    infix_symbol = "issubset"
    infix_symbol_latex = r"\subseteq"
    tactics: list[Tactic] = []

    def __init__(
        self,
        left: Set,
        right: Set,
        is_assumption: bool = False,
        description: str = "",
        **kwargs,
    ) -> None:
        self.right: Set = right
        self.left: Set = left
        name = f"{left.name} is a subset of {right.name}"
        super().__init__(
            left,
            right,
            is_assumption=is_assumption,
            description=description,
            **kwargs,
        )

    def copy(self) -> Self:
        return self.__class__(
            self.left.copy(),
            self.right.copy(),
            is_assumption=self.is_assumption,
            description=self.description,
            _is_proven=self._is_proven,
            _assumptions=self.from_assumptions,
            _inference=self.deduced_from,
        )

    def to_forall(self) -> Forall[Implies[IsContainedIn, IsContainedIn]]:
        """
        If self is `A issubset B`, return `forall x: x in A -> x in B`
        """
        from pylogic.variable import Variable
        from pylogic.proposition.quantified.forall import Forall
        from pylogic.inference import Inference

        x = Variable("x")
        left = IsContainedIn(x, self.left)
        right = IsContainedIn(x, self.right)
        return Forall(
            x,
            left.implies(right),
            _is_proven=self.is_proven,
            _assumptions=get_assumptions(self),
            _inference=Inference(self, rule="to_forall"),
        )
