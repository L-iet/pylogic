from __future__ import annotations

from typing import TYPE_CHECKING, Callable, Iterable, Literal, Self, TypeVar, overload

import sympy as sp

from pylogic.proposition.contradiction import Contradiction
from pylogic.structures.collection import Collection

if TYPE_CHECKING:
    from fractions import Fraction

    from pylogic.expressions.expr import Expr
    from pylogic.proposition.proposition import Proposition
    from pylogic.proposition.relation.contains import IsContainedIn
    from pylogic.proposition.relation.equals import Equals
    from pylogic.structures.set_ import Set
    from pylogic.symbol import Symbol

    Numeric = Fraction | int | float
    PBasic = Symbol | Numeric
    Unevaluated = Symbol | Set | Expr
    Term = Unevaluated | Numeric
    T = TypeVar("T", bound=Term)
    C = TypeVar("C", bound="Set")


class Set(metaclass=Collection):
    """
    A set `S` is a collection of elements. This is equivalent to
    `Class0`.
    In pylogic/structures/class_.py, we define `Sets`, the `Class1` of all sets.


    You can prove the proposition `x in S` either using the containment_function,
    i.e. `S.containment_function(x) == True` using `S.contains(x).by_inspection()`, or
    by supplying a proven proposition `p` of `S.predicate(x)` to
    `S.contains(x).by_predicate(p)`.

    `S` is the set of all x such that `S.predicate(x)` is a true proposition,
    and vice-versa.
    That is, `S.predicate(x) <-> x in S`.

    `Set()` gives the empty set.
    """

    level = 0  # level of the set in the hierarchy of Classes

    @overload
    def __new__(cls) -> Set: ...
    @overload
    def __new__(cls: type[C], name: str, *args, **kwargs) -> C: ...
    def __new__(cls, *args, **kwargs):
        if len(args) == 0 and len(kwargs) == 0:
            global EmptySet
            return EmptySet
        return object.__new__(cls)

    def __init__(
        self,
        name: str | None = None,
        elements: Iterable[Term] | None = None,
        containment_function: Callable[[Term], bool] | None = None,
        predicate: Callable[[Term], Proposition] | None = None,
        illegal_occur_check: bool = True,
    ):
        if name is not None:
            name = name.strip()
            sympy_set = sp.Set(name)
            assert " " not in name, "Set name cannot contain spaces"
            self.name = name or str(sympy_set)
            self.sympy_set = sympy_set
            self.elements: set[Term] = set(elements) if elements else set()
            self._containment_function: Callable[[Term], bool] = (
                containment_function or (lambda x: x in self.elements)
            )
            if illegal_occur_check:
                self.illegal_occur_check(containment_function, predicate)

            self._predicate = predicate
            self.is_real = False
        elif any(x is not None for x in (elements, containment_function, predicate)):
            raise ValueError("Must provide a name for the set.")
        self._init_args = ()
        self._init_kwargs = {
            "name": name,
            "elements": elements,
            "containment_function": containment_function,
            "predicate": predicate,
            "illegal_occur_check": illegal_occur_check,
        }

    def illegal_occur_check(
        self,
        containment_function: Callable[[Term], bool] | None = None,
        predicate: Callable[[Term], Proposition] | None = None,
    ) -> Literal[False]:
        """
        Perform the illegal occurrence check on the containment function and predicate.
        Returns False if no illegal occurrences are found.
        Raises a ValueError if an illegal occurrence is found.

        https://en.wikipedia.org/wiki/Axiom_schema_of_specification#In_Quine%27s_New_Foundations
        We follow this New Foundations specification where
        we can have a set of all sets, but the argument of the containment function
        or predicate cannot appear on both sides of an IsContainedIn statement,
        avoiding Russell's paradox.


        Note that we can still have sets that contain themselves,
        and (obviously) sets that do not contain themselves.


        We check for this in a Set or Class{n} instance `S` by checking if
        `S.containment_function(S)` recurses forever
        or if a proposition of the form `Expr(...S...) in Expr(...S...)`
        appears in `S.predicate(S)`
        If an (AttributeError, TypeError, ValueError) occurs during these checks,
        we assume the functions are valid, since it means `S` does not match an
        implicit pattern.
        """
        if containment_function is not None:
            try:
                containment_function(self)
            except RecursionError as e:
                raise ValueError(
                    "Invalid containment function supplied.\n \
See https://en.wikipedia.org/wiki/Axiom_schema_of_specification#In_Quine%27s_New_Foundations"
                ) from e
            except (AttributeError, TypeError, ValueError):
                pass
        if predicate is not None:
            try:
                illegal_occur = self.illegal_occur_check_pred(predicate(self))
            except (AttributeError, TypeError, ValueError):
                illegal_occur = False
            if illegal_occur:
                raise ValueError(
                    "Invalid predicate supplied.\n \
See https://en.wikipedia.org/wiki/Axiom_schema_of_specification#In_Quine%27s_New_Foundations"
                )
        return False

    def illegal_occur_check_pred(self, predicate_of_self: Proposition) -> bool:
        from pylogic.helpers import find_first
        from pylogic.proposition._junction import _Junction
        from pylogic.proposition.implies import Implies
        from pylogic.proposition.not_ import Not

        # TODO: Add Iff import
        from pylogic.proposition.quantified.quantified import _Quantified
        from pylogic.proposition.relation.contains import IsContainedIn
        from pylogic.symbol import Symbol

        if isinstance(predicate_of_self, IsContainedIn):
            if isinstance(predicate_of_self.left, (Set, Symbol)):
                occurs_in_left = predicate_of_self.left == self
            else:  # Expr
                occurs_in_left = self in predicate_of_self.left.sets
            if isinstance(predicate_of_self.right, (Set, Symbol)):
                occurs_in_right = predicate_of_self.right == self
            else:  # Expr
                occurs_in_right = self in predicate_of_self.right.sets
            return occurs_in_left and occurs_in_right
        elif isinstance(predicate_of_self, Implies):
            return self.illegal_occur_check_pred(
                predicate_of_self.antecedent
            ) or self.illegal_occur_check_pred(predicate_of_self.consequent)
        elif isinstance(predicate_of_self, Not):
            return self.illegal_occur_check_pred(predicate_of_self.negated)
        elif isinstance(predicate_of_self, _Junction):
            return (
                find_first(
                    lambda p: self.illegal_occur_check_pred(p),
                    predicate_of_self.propositions,
                )[1]
                is not None
            )
        elif isinstance(predicate_of_self, _Quantified):
            return self.illegal_occur_check_pred(predicate_of_self.inner_proposition)
        else:
            return False

    def eval_same(self, other: object) -> bool:
        if isinstance(other, sp.Set):
            return self.sympy_set == other
        elif not isinstance(other, Set):
            return False
        return self.sympy_set == other.sympy_set

    def __eq__(self, other: Set) -> bool:
        """
        Check if two sets are structurally equal.
        """
        if not isinstance(other, Set):
            return False
        return self.sympy_set == other.sympy_set

    def equals(self, other: Term, **kwargs) -> Equals:
        from pylogic.proposition.relation.equals import Equals

        return Equals(self, other, **kwargs)

    def dummy_eq(self, other: object) -> bool:
        if not isinstance(other, Set):
            return False
        return self.sympy_set == other.sympy_set

    def contains(
        self, other: T, is_assumption: bool = False, **kwargs
    ) -> IsContainedIn[T, Self]:
        from pylogic.proposition.relation.contains import IsContainedIn

        """elementhood"""

        return IsContainedIn(other, self, is_assumption=is_assumption, **kwargs)

    def predicate(self, x: Term) -> Proposition:
        from pylogic.proposition.relation.contains import IsContainedIn

        if self._predicate is None:
            return IsContainedIn(x, self)
        return self._predicate(x)

    def evaluate(self) -> Set:
        return self

    def to_sympy(self) -> sp.Set:
        return self.sympy_set

    def containment_function(self, x: Term) -> bool:
        return self._containment_function(x)

    def __repr__(self) -> str:
        return f"Set_{self.name}"

    def __str__(self) -> str:
        return self.name

    def __copy__(self) -> "Set":
        return self.copy()

    def __hash__(self) -> int:
        return hash(("Set", self.name, self.containment_function))

    def _latex(self, printer=None) -> str:
        return rf"\text{{{self.name}}}"

    def _repr_latex_(self) -> str:
        return f"$${self._latex()}$$"

    def copy(self) -> Self:
        return self.__class__(*self._init_args, **self._init_kwargs)

    def deepcopy(self) -> Self:
        return self.__class__(*self._init_args, **self._init_kwargs)


EmptySet = Set(
    "EmptySet",
    containment_function=lambda x: False,
    predicate=lambda x: Contradiction(),
    illegal_occur_check=False,
)

UniversalSet = Set(
    "UniversalSet",
    containment_function=lambda x: not x.__class__.__name__.startswith("Collection"),
    illegal_occur_check=False,
)

# Integers = Set(sympy_set=sp.Integers)
# Rationals = Set(sympy_set=sp.Rationals)
# Reals = Set(sympy_set=sp.Reals)
# Naturals = Set(sympy_set=sp.Naturals)
# Naturals0 = Set(sympy_set=sp.Naturals0)
# Graphs = Set(name="Graphs", containment_function=lambda x: x.is_graph)  # type: ignore
# Matrices = Set(name="Matrices")
# Vectors = Set(name="Vectors")
# Functions = Set(name="Functions")
# Sequences = Set(name="Sequences", containment_function=lambda x: x.is_sequence)  # type: ignore
# Lists = Set(name="Lists", containment_function=lambda x: x.is_list) # type: ignore
# Pairs = Set(name="Pairs", containment_function=lambda x: x.is_pair) # type: ignore
