from __future__ import annotations

from typing import TYPE_CHECKING, Any, Self, TypedDict, TypeVar

from pylogic.proposition.proposition import get_assumptions
from pylogic.proposition.relation.binaryrelation import BinaryRelation

if TYPE_CHECKING:
    from pylogic.expressions.sequence_term import SequenceTerm
    from pylogic.proposition.implies import Implies
    from pylogic.proposition.proposition import Proposition
    from pylogic.proposition.quantified.forall import Forall
    from pylogic.proposition.relation.contains import IsContainedIn
    from pylogic.structures.collection import Class
    from pylogic.structures.set_ import Set
    from pylogic.variable import Variable

    T = TypeVar("T", bound=Variable | SequenceTerm | Set | Class)
    U = TypeVar("U", bound=Variable | SequenceTerm | Set | Class)
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
        assert (
            self.left.is_set and self.right.is_set
        ), f"Both left and right must be sets, left: {left}, left.is_set: {left.is_set}, \
right: {right}, right.is_set: {right.is_set}"

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

    def by_inspection(self) -> Self:
        """
        Logical tactic. If self is already proven, self is `A issubset A`,
        or the predicate of self.left logically implies that any variable x in self.left is in self.right,
        return self but proven.
        """
        from pylogic.helpers import getkey
        from pylogic.inference import Inference
        from pylogic.proposition.and_ import And
        from pylogic.proposition.relation.contains import IsContainedIn
        from pylogic.variable import Variable

        proven = False

        # already proven
        if self in self.left.knowledge_base:
            return getkey(self.left.knowledge_base, self)
        if self.left == self.right:
            proven = True

        # seeing if we can derive x in right from assuming x in left
        if hasattr(self.left, "predicate"):
            x = Variable("x")
            left_pred = self.left.predicate(x)
            # left_pred._set_is_assumption(True)
            match left_pred:
                case IsContainedIn(
                    left=x1, right=right
                ) if x1 == x and right == self.right:
                    proven = True
                case And(propositions=props) if IsContainedIn(x, self.right) in props:
                    proven = True
        if proven:
            new_p = self.copy()
            new_p._set_is_proven(True)
            new_p.from_assumptions = set()
            new_p.deduced_from = Inference(self, rule="by_inspection")
            return new_p
        raise ValueError(f"Cannot prove that {self.left} is a subset of {self.right}")
