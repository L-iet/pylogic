from __future__ import annotations

from typing import TYPE_CHECKING, Any, Self, TypedDict, TypeVar

from pylogic import Term
from pylogic.inference import Inference
from pylogic.proposition.relation.binaryrelation import BinaryRelation

if TYPE_CHECKING:
    from pylogic.expressions.sequence_term import SequenceTerm
    from pylogic.proposition.and_ import And
    from pylogic.proposition.not_ import Not
    from pylogic.proposition.or_ import Or
    from pylogic.proposition.proposition import Proposition
    from pylogic.proposition.relation.equals import Equals
    from pylogic.proposition.relation.subsets import IsSubsetOf
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

InferenceRule = TypedDict("InferenceRule", {"name": str, "arguments": list[str]})


class IsContainedIn(BinaryRelation[T, U]):
    is_transitive = False
    name = "IsContainedIn"
    infix_symbol = "in"
    infix_symbol_latex = r"\in"
    _inference_rules: list[InferenceRule] = [
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
            self._set_is_inferred(True)

        self._set_init_inferred_attrs()

    @property
    def element(self) -> T:
        return self.left

    def _set_is_inferred(self, value: bool) -> None:
        sets_and_attrs = {
            "Naturals": ["is_natural"],
            "Integers": ["is_integer"],
            "Rationals": ["is_rational"],
            "Reals": ["is_real"],
            "AllFiniteSequences": ["is_sequence", "is_finite"],
        }
        if value:
            # TODO: add more here
            if self.right.name in sets_and_attrs:
                for attr in sets_and_attrs[self.right.name]:
                    setattr(self.left, attr, True)
            self.left.knowledge_base.add(self)
            self.left.sets_contained_in.add(self.right)
            self.right.elements.add(self.left)
        else:
            if self.right.name in sets_and_attrs:
                for attr in sets_and_attrs[self.right.name]:
                    setattr(self.left, attr, None)
            self.left.knowledge_base.discard(self)
            self.left.sets_contained_in.discard(self.right)
            self.right.elements.discard(self.left)

    # def _set_is_proven(self, value: bool, **kwargs) -> None:
    #     super()._set_is_proven(value, **kwargs)
    #     if value:
    #         self._set_is_inferred(True)
    #     elif not (self.is_axiom or self.is_assumption):
    #         self._set_is_inferred(False)

    # def _set_is_assumption(self, value: bool, **kwargs) -> None:
    #     super()._set_is_assumption(value, **kwargs)
    #     # TODO: fix this. I'm still getting some dummy variables in
    #     # set's elements although we called followed_from with this prop
    #     # update Oct 11 2024, did I fix this?
    #     if value:
    #         self._set_is_inferred(True)
    #     elif not (self._is_proven or self.is_axiom):
    #         self._set_is_inferred(False)

    # def _set_is_axiom(self, value: bool) -> None:
    #     super()._set_is_axiom(value)
    #     if value:
    #         self._set_is_inferred(True)
    #     elif not (self._is_proven or self.is_assumption):
    #         self._set_is_inferred(False)

    def by_containment_func(self) -> Self:
        """Logical inference rule. Use the set's containment function to prove that it
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
        """Logical inference rule. Use the set's predicate function to prove that it
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

    def by_inspection_check(self) -> bool | None:
        return (
            True
            if self in self.left.knowledge_base
            or self.right.containment_function(self.left)
            else None
        )

    def by_definition(self) -> Self:
        """Logical inference rule. Prove that the element is in the set by definition."""
        return self.by_containment_func()

    def thus_predicate(self) -> Proposition:
        """Logical inference rule. Given that the set contains the element, return
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
        Logical inference rule. Given self = x in S is proven, return a proof that S is not empty.
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
        """Logical inference rule. Given x in Union[A, B, C],
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
        """Logical inference rule. Given x in Intersection[A, B, C],
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

    def thus_contained_in_b(self, a_is_subset_b: IsSubsetOf) -> IsContainedIn:
        """Logical inference rule. If self is proven and of the form `x in A` and `A issubset B`
        is given, returns a proven proposition of the form `x in B`"""
        from pylogic.inference import Inference
        from pylogic.proposition.proposition import get_assumptions
        from pylogic.proposition.relation.subsets import IsSubsetOf

        assert self.is_proven, f"{self} is not proven"
        assert isinstance(
            a_is_subset_b, IsSubsetOf
        ), f"{a_is_subset_b} is not an `IsSubsetOf`"
        assert a_is_subset_b.is_proven, f"{a_is_subset_b} is not proven"
        assert (
            self.right == a_is_subset_b.left
        ), f"{self.right} in {self} is not the same as {a_is_subset_b.left} in {a_is_subset_b}"

        return IsContainedIn(
            self.left,
            a_is_subset_b.right,
            _is_proven=True,
            _assumptions=get_assumptions(self).union(get_assumptions(a_is_subset_b)),
            _inference=Inference(self, rule="thus_contained_in_b"),
        )
