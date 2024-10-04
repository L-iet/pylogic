from __future__ import annotations

from typing import TYPE_CHECKING, Any, Self, TypedDict, TypeVar

from pylogic import Term
from pylogic.proposition.proposition import get_assumptions
from pylogic.proposition.relation.binaryrelation import BinaryRelation

if TYPE_CHECKING:
    from pylogic.proposition.implies import Implies
    from pylogic.proposition.proposition import Proposition
    from pylogic.proposition.quantified.forall import Forall
    from pylogic.proposition.relation.contains import IsContainedIn
    from pylogic.structures.collection import Class
    from pylogic.structures.set_ import Set
    from pylogic.variable import Variable

    T = TypeVar("T", bound=Variable | Set | Class)
    U = TypeVar("U", bound=Variable | Set | Class)
else:
    T = Any
    U = Any
TProposition = TypeVar("TProposition", bound="Proposition")
UProposition = TypeVar("UProposition", bound="Proposition")
Tactic = TypedDict("Tactic", {"name": str, "arguments": list[str]})


class IsSubsetOf(BinaryRelation[T, U]):
    is_transitive = True
    name = "IsSubsetOf"
    infix_symbol = "issubset"
    infix_symbol_latex = r"\subseteq"
    tactics: list[Tactic] = []

    def __init__(
        self,
        left: T,
        right: U,
        is_assumption: bool = False,
        description: str = "",
        **kwargs,
    ) -> None:
        self.right: U = right
        self.left: T = left
        name = f"{left} is a subset of {right}"
        super().__init__(
            left,
            right,
            is_assumption=is_assumption,
            description=description,
            **kwargs,
        )

    def copy(self) -> Self:
        return self.__class__(
            self.left,
            self.right,
            is_assumption=self.is_assumption,
            description=self.description,
            _is_proven=self._is_proven,
            _assumptions=self.from_assumptions,
            _inference=self.deduced_from,
        )

    def deepcopy(self) -> Self:
        return self.__class__(
            self.left.deepcopy(),
            self.right.deepcopy(),
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
        from pylogic.inference import Inference
        from pylogic.proposition.quantified.forall import Forall
        from pylogic.variable import Variable

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

    def by_empty(self) -> Self:
        """
        Logical tactic.
        If self is `EmptySet issubset A`, return self but proven
        """
        from pylogic.inference import Inference
        from pylogic.structures.set_ import EmptySet

        assert self.left == EmptySet, "left must be EmptySet"
        new_p = self.copy()
        new_p._set_is_proven(True)
        new_p.from_assumptions = set()
        new_p.deduced_from = Inference(self, rule="by_empty")
        return new_p
