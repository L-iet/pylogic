from __future__ import annotations
from pylogic.proposition.relation.binaryrelation import BinaryRelation
from typing import TYPE_CHECKING, TypedDict, TypeVar

if TYPE_CHECKING:
    from pylogic.proposition.proposition import Proposition
    from pylogic.variable import Variable
    from pylogic.symbol import Symbol
    from pylogic.structures.sets import Set
    from pylogic.proposition.relation.contains import IsContainedIn
    from pylogic.proposition.implies import Implies
    from pylogic.proposition.quantified.forall import Forall
    from sympy import Basic

    Term = Variable | Symbol | Set | Basic | int | float
from sympy.printing.latex import LatexPrinter

latex_printer = LatexPrinter()

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
        _is_proven: bool = False,
    ) -> None:
        self.right: Set = right
        self.left: Set = left
        name = f"{left.name} is a subset of {right.name}"
        super().__init__(
            left, right, is_assumption=is_assumption, _is_proven=_is_proven
        )

    def copy(self) -> Subset:
        return Subset(
            self.left.copy(),
            self.right.copy(),
            is_assumption=self.is_assumption,
            _is_proven=self.is_proven,
        )

    def to_forall(self) -> Forall[Implies[IsContainedIn, IsContainedIn]]:
        """
        If self is `A issubset B`, return `forall x: x in A -> x in B`
        """
        from pylogic.variable import Variable
        from pylogic.proposition.quantified.forall import Forall

        x = Variable("x")
        left = IsContainedIn(x, self.left)
        right = IsContainedIn(x, self.right)
        return Forall(
            x,
            left.implies(right),
            is_assumption=self.is_assumption,
            _is_proven=self.is_proven,
        )
