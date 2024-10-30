from __future__ import annotations

from typing import TYPE_CHECKING, Any, Self, TypedDict, TypeVar

from pylogic import Term
from pylogic.expressions.expr import to_sympy
from pylogic.inference import Inference
from pylogic.proposition.relation.binaryrelation import BinaryRelation

if TYPE_CHECKING:
    from pylogic.expressions.sequence_term import SequenceTerm
    from pylogic.proposition.and_ import And
    from pylogic.proposition.not_ import Not
    from pylogic.proposition.or_ import Or
    from pylogic.proposition.proposition import Proposition
    from pylogic.proposition.relation.equals import Equals
    from pylogic.structures.collection import Class
    from pylogic.structures.sequence import Sequence
    from pylogic.structures.set_ import Set
    from pylogic.variable import Variable

    U = TypeVar("U", bound=Variable | Set | Class | SequenceTerm)
else:
    Set = Any
    Term = Any
    U = Any
T = TypeVar("T", bound=Term)

Tactic = TypedDict("Tactic", {"name": str, "arguments": list[str]})


class IsContainedIn(BinaryRelation[T, U]):
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
        right: U,
        is_assumption: bool = False,
        description: str = "",
        **kwargs,
    ) -> None:
        self.right: U = right
        self.left: T = left
        super().__init__(
            left,
            right,
            is_assumption=is_assumption,
            description=description,
            **kwargs,
        )
        if (
            kwargs.get("_is_proven")
            or kwargs.get("is_assumption")
            or kwargs.get("is_axiom")
        ):
            self._set_is_inferred_true()

    @property
    def element(self) -> T:
        return self.left

    def _set_is_inferred_true(self) -> None:
        super()._set_is_inferred_true()
        # TODO: add more here
        if self.right.name in {"Naturals", "Integers", "Rationals", "Reals"}:
            substr = self.right.name[:-1].lower()
            setattr(self.left, f"_is_{substr}", True)
        self.left.knowledge_base.add(self)
        self.right.elements.add(self.left)

    def _set_is_proven(self, value: bool) -> None:
        super()._set_is_proven(value)
        if value:
            self._set_is_inferred_true()
        elif not (self.is_axiom or self.is_assumption):
            self.right.elements.discard(self.left)
            self.left.knowledge_base.discard(self)

    def _set_is_assumption(self, value: bool) -> None:
        super()._set_is_assumption(value)
        # TODO: fix this. I'm still getting some dummy variables in
        # set's elements although we called followed_from with this prop
        # update Oct 11 2024, did I fix this?
        if value:
            self._set_is_inferred_true()
        else:
            if not (self._is_proven or self.is_axiom):
                self.right.elements.discard(self.left)
                self.left.knowledge_base.discard(self)

    def _set_is_axiom(self, value: bool) -> None:
        super()._set_is_axiom(value)
        if value:
            self._set_is_inferred_true()
        elif not (self._is_proven or self.is_assumption):
            self.right.elements.discard(self.left)
            self.left.knowledge_base.discard(self)

    def by_containment_func(self) -> Self:
        """Logical tactic. Use the set's containment function to prove that it
        contains the element
        """
        try:
            if self.right.containment_function(self.left):
                return IsContainedIn(
                    self.element,
                    self.right,
                    _is_proven=True,
                    _assumptions=set(),
                    _inference=Inference(self, rule="by_containment_func"),
                )  # type: ignore
        except Exception as e:
            raise ValueError(
                f"Cannot prove that {self.right} contains {self.left}\nThis was a result of\n{e}"
            )
        else:
            raise ValueError(f"Cannot prove that {self.right} contains {self.left}")

    def by_predicate(self, proven_predicate: Proposition) -> Self:
        """Logical tactic. Use the set's predicate function to prove that it
        contains the element
        """
        # For sequence s = self.right, self.left would need to be a natural number n
        # representing the index of the sequence term.
        # However, (n in s).by_predicate(...) would then be nonsensical.
        assert self.right.is_set, f"{self.right} is not a set"
        try:
            if (
                proven_predicate.is_proven
                and self.right.predicate(self.left) == proven_predicate
            ):
                return IsContainedIn(
                    self.element,
                    self.right,
                    _is_proven=True,
                    _assumptions=set(),
                    _inference=Inference(self, rule="by_predicate"),
                )  # type: ignore
        except Exception as e:
            raise ValueError(
                f"Cannot prove that {self.right} contains {self.left}\nThis was a result of\n{e}"
            )
        else:
            raise ValueError(f"Cannot prove that {self.right} contains {self.left}")

    def by_inspection(self) -> Self:
        """Logical tactic. Use the set's containment function and sympy set to
        prove that it contains the element.
        """
        from pylogic.helpers import getkey

        if self in self.left.knowledge_base:
            return getkey(self.left.knowledge_base, self)  # type: ignore
        return self.by_containment_func()

    def thus_predicate(self) -> Proposition:
        """Logical tactic. Given that the set contains the element, return
        the predicate that the element satisfies.
        """
        assert self.is_proven, f"{self} is not proven"
        assert self.right.is_set, f"{self.right} is not a set"  # see by_predicate
        from pylogic.proposition.proposition import get_assumptions

        res = self.right.predicate(self.left)
        res._set_is_proven(True)
        res.from_assumptions = get_assumptions(self)
        res.deduced_from = Inference(self, rule="thus_predicate")
        return res

    def thus_not_empty(self) -> Not[Equals]:
        """
        Logical tactic. Given self = x in S is proven, return a proof that S is not empty.
        """
        assert self.is_proven, f"{self} is not proven"
        from pylogic.proposition.not_ import Not
        from pylogic.proposition.proposition import get_assumptions
        from pylogic.proposition.relation.equals import Equals
        from pylogic.structures.set_ import EmptySet

        self.right.is_empty = False
        res = Not(
            Equals(self.right, EmptySet),
            _is_proven=True,
            _inference=Inference(self, rule="thus_not_empty"),
            _assumptions=get_assumptions(self),
        )
        self.right.knowledge_base.add(res)
        return res

    def thus_contained_in_at_least_one(self) -> Or[IsContainedIn, ...]:
        """Logical tactic. Given x in Union[A, B, C],
        return a proof that x in A or x in B or x in C"""
        assert self.is_proven, f"{self} is not proven"
        from pylogic.proposition.or_ import Or
        from pylogic.structures.set_ import Union

        assert isinstance(self.right, Union), f"{self.right} is not a Union"
        return Or(
            *[
                IsContainedIn(self.left, set_) for set_ in self.right.sets
            ],  # type: ignore
            _is_proven=True,
            _assumptions=self.from_assumptions,
            _inference=Inference(self, rule="thus_contained_in_at_least_one"),
        )

    def thus_contained_in_all(self) -> And[IsContainedIn, ...]:
        """Logical tactic. Given x in Intersection[A, B, C],
        return a proof that x in A and x in B and x in C"""
        assert self.is_proven, f"{self} is not proven"
        from pylogic.proposition.and_ import And
        from pylogic.structures.set_ import Intersection

        assert isinstance(
            self.right, Intersection
        ), f"{self.right} is not an Intersection"
        return And(
            *[
                IsContainedIn(self.left, set_) for set_ in self.right.sets
            ],  # type: ignore
            _is_proven=True,
            _assumptions=self.from_assumptions,
            _inference=Inference(self, rule="thus_contained_in_all"),
        )
