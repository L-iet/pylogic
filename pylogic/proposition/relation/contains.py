from __future__ import annotations

from typing import TYPE_CHECKING, Any, Self, TypedDict, TypeVar

from pylogic import Term
from pylogic.expressions.expr import to_sympy
from pylogic.inference import Inference
from pylogic.proposition.relation.binaryrelation import BinaryRelation

if TYPE_CHECKING:
    from pylogic.proposition.and_ import And
    from pylogic.proposition.or_ import Or
    from pylogic.proposition.proposition import Proposition
    from pylogic.structures.collection import Class
    from pylogic.structures.set_ import Set
    from pylogic.variable import Variable

    U = TypeVar("U", bound=Variable | Set | Class)
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
            self.right.elements.add(self.left)

    @property
    def set_(self) -> U:
        return self.right

    @property
    def element(self) -> T:
        return self.left

    def _set_is_proven(self, value: bool) -> None:
        if value:
            self.right.elements.add(self.left)
        elif not (self.is_axiom or self.is_assumption):
            self.right.elements.discard(self.left)
        super()._set_is_proven(value)

    def _set_is_assumption(self, value: bool) -> None:
        # TODO: fix this. I'm still getting some dummy variables in
        # set's elements although we called followed_from with this prop
        if value:
            self.right.elements.add(self.left)
        else:
            if not (self._is_proven or self.is_axiom):
                self.right.elements.discard(self.left)
        super()._set_is_assumption(value)

    def _set_is_axiom(self, value: bool) -> None:
        if value:
            self.right.elements.add(self.left)
        elif not (self._is_proven or self.is_assumption):
            self.right.elements.discard(self.left)
        super()._set_is_axiom(value)

    def by_containment_func(self) -> Self:
        """Logical tactic. Use the set's containment function to prove that it
        contains the element
        """
        try:
            if self.right.containment_function(self.left):
                return IsContainedIn(
                    self.element,
                    self.set_,
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
        try:
            if (
                proven_predicate.is_proven
                and self.right.predicate(self.left) == proven_predicate
            ):
                return IsContainedIn(
                    self.element,
                    self.set_,
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

    def by_sympy_def(self) -> Self:
        """Logical tactic. Use sympy's definition of the set to prove that
        it contains the element.
        """
        try:
            if self.left in self.right.elements or (
                hasattr(self.right, "sympy_set")  # in case self.right is a Class{n}
                and to_sympy(self.left) in self.right.sympy_set  # type: ignore
            ):
                return IsContainedIn(
                    self.element,
                    self.set_,
                    is_assumption=self.is_assumption,
                    _is_proven=True,
                    _assumptions=set(),
                    _inference=Inference(self, rule="by_def"),
                )  # type: ignore
        except (TypeError, NotImplementedError) as e:
            raise ValueError(
                f"Cannot prove that {self.right} contains {self.left}\nThis was a result of\n{e}"
            )
        raise ValueError(f"Cannot prove that {self.right} contains {self.left}")

    def by_inspection(self) -> Self:
        """Logical tactic. Use the set's containment function and sympy set to
        prove that it contains the element.
        """
        try:
            return self.by_containment_func()
        except ValueError:
            return self.by_sympy_def()

    def thus_predicate(self) -> Proposition:
        """Logical tactic. Given that the set contains the element, return
        the predicate that the element satisfies.
        """
        assert self.is_proven, f"{self} is not proven"

        return self.right.predicate(self.left)

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
