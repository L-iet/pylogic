from __future__ import annotations

from typing import (
    TYPE_CHECKING,
    Any,
    Callable,
    Iterable,
    Literal,
    Self,
    TypeVar,
    overload,
)

import sympy as sp

from pylogic import Term
from pylogic.proposition.contradiction import Contradiction
from pylogic.structures.collection import Collection

if TYPE_CHECKING:
    from pylogic.expressions.expr import Expr
    from pylogic.expressions.sequence_term import SequenceTerm
    from pylogic.proposition.proposition import Proposition
    from pylogic.proposition.relation.contains import IsContainedIn
    from pylogic.proposition.relation.equals import Equals
    from pylogic.proposition.relation.subsets import IsSubsetOf
    from pylogic.structures.sequence import Sequence
    from pylogic.symbol import Symbol
    from pylogic.variable import Variable

T = TypeVar("T", bound=Term)
C = TypeVar("C", bound="Set")

# TODO: implement __eq__, __hash__, __repr__ and latex methods for all classes


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
    def __new__(cls: type[C], *args, **kwargs) -> C: ...
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
        latex_str: str | None = None,
    ):
        from pylogic.helpers import python_to_pylogic

        if name is not None:
            name = name.strip()
            sympy_set = sp.Set(name)
            assert " " not in name, "Set name cannot contain spaces"
            self.name = name or str(sympy_set)
            self.sympy_set = sympy_set
            self.elements: set[Term] = (
                set(map(python_to_pylogic, elements)) if elements else set()
            )  # type: ignore
            self._containment_function: Callable[[Term], bool] | None = (
                containment_function
            )
            if illegal_occur_check:
                self.illegal_occur_check(containment_function, predicate)

            self._predicate = predicate
        elif any(x is not None for x in (elements, containment_function, predicate)):
            raise ValueError("Must provide a name for the set.")
        self.is_finite: bool | None = None
        self.is_union: bool | None = None
        self.is_intersection: bool | None = None
        self.is_cartes_product: bool | None = None
        self.is_cartes_power: bool | None = None
        self.is_real = False
        self.is_set = True
        self.is_set_ = True
        self._init_args = ()
        self._init_kwargs = {
            "name": name,
            "elements": elements,
            "containment_function": containment_function,
            "predicate": predicate,
            "illegal_occur_check": illegal_occur_check,
        }
        self.knowledge_base: set[Proposition] = set()
        self.is_empty: bool | None = None
        self.latex_str = latex_str or self.name

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
        # TODO: add conditions to this
        if not isinstance(other, Set):
            return NotImplemented
        return self.name == other.name

    def __contains__(self, item: Any) -> bool:
        return self.containment_function(item)

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

    def countable(self, is_assumption: bool = False, **kwargs) -> Exists:
        # TODO: make this  ExistsInSet where set is the class of
        # all sequences
        from pylogic.proposition.quantified.exists import Exists
        from pylogic.structures.set_ import SeqSet
        from pylogic.variable import Variable

        s = Variable("s", sequence=True)
        return Exists(
            s,
            self.equals(SeqSet(s)),
            description=f"{self} is countable",
            is_assumption=is_assumption,
            **kwargs,
        )

    def predicate(self, x: Term) -> Proposition:
        from pylogic.proposition.relation.contains import IsContainedIn

        if self._predicate is None:
            return IsContainedIn(x, self)
        return self._predicate(x)

    def is_subset_of(
        self, other: Set | Variable | SequenceTerm, **kwargs
    ) -> IsSubsetOf:
        from pylogic.proposition.relation.subsets import IsSubsetOf

        return IsSubsetOf(self, other, **kwargs)

    def evaluate(self) -> Set:
        return self

    def to_sympy(self) -> sp.Set:
        return self.sympy_set

    def containment_function(self, x: Term) -> bool:
        if x in self.elements:
            return True
        elif self._containment_function:
            res = self._containment_function(x)
            self.elements.add(x) if res else None
            return res
        return False

    def __repr__(self) -> str:
        return f"Set_{self.name}"

    def __str__(self) -> str:
        return self.name

    def __copy__(self) -> "Set":
        return self.copy()

    def __hash__(self) -> int:
        return hash(("Set", self.name, self.containment_function))

    def _latex(self, printer=None) -> str:
        return self.latex_str

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
    latex_str=r"\emptyset",
)
EmptySet.is_empty = True

UniversalSet = Set(
    "UniversalSet",
    containment_function=lambda x: not x.__class__.__name__.startswith("Collection"),
    illegal_occur_check=False,
    latex_str=r"\mathcal{U}",
)
UniversalSet.is_empty = False

SingletonEmpty = Set(
    "SingletonEmpty",
    elements={EmptySet},
    illegal_occur_check=False,
    latex_str=r"\{\emptyset\}",
)
SingletonEmpty.is_empty = False


class FiniteSet(Set):
    def __init__(
        self,
        name: str | None = None,
        elements: Iterable[Term] | None = None,
        **kwargs,
    ):
        super().__init__(name=name, elements=elements, **kwargs)
        self.is_finite = True

    def __eq__(self, other: FiniteSet) -> bool:
        if not isinstance(other, FiniteSet):
            return NotImplemented
        return self.elements == other.elements

    def __hash__(self) -> int:
        elements = tuple(sorted(self.elements, key=lambda x: str(x)))
        return hash(("FiniteSet", self.name, elements))

    def __str__(self) -> str:
        return str(self.elements)

    def __repr__(self) -> str:
        return f"FiniteSet({self.elements})"


class Union(Set):
    """
    Represents the union of finitely many or countably-infinitely many sets.
    """

    def __init__(
        self,
        sets: Sequence[Set | Variable],
        name: str | None = None,
        **kwargs,
    ):
        from pylogic.proposition.quantified.exists import ExistsInSet
        from pylogic.theories.natural_numbers import Naturals
        from pylogic.variable import Variable

        pred0 = kwargs.pop("predicate", None)

        k = Variable("k")
        pred = lambda x: (
            ExistsInSet(k, Naturals, x.is_in(sets[k]))
            if pred0 is None
            else ExistsInSet(k, Naturals, x.is_in(sets[k])).and_(pred0(x))
        )
        latex_str = kwargs.pop("latex_str", None) or rf"\bigcup {sets._latex()}"
        super().__init__(name=name, predicate=pred, latex_str=latex_str, **kwargs)
        self.set_sequence: Sequence[Set | Variable] = sets
        self.is_union = True

    def __eq__(self, other: Union) -> bool:
        if not isinstance(other, Union):
            return NotImplemented
        return self.set_sequence == other.set_sequence

    def __hash__(self) -> int:
        return hash(("Union", self.name, self.set_sequence))

    def __str__(self) -> str:
        return f"Union({self.set_sequence})"

    def __repr__(self) -> str:
        return f"Union({self.set_sequence!r})"


class FiniteUnion(Union):
    """
    Represents a union of a specified number of sets.
    """

    @overload
    def __new__(cls) -> Set: ...
    @overload
    def __new__(
        cls, sets: Iterable[Set | Variable], name: str | None = None
    ) -> FiniteUnion: ...
    def __new__(
        cls,
        sets: Iterable[Set | Variable] | None = None,
        name: str | None = None,
        **kwargs,
    ) -> FiniteUnion | Set:
        if not sets:
            return EmptySet
        return object.__new__(cls)

    def __init__(
        self,
        sets: Iterable[Set | Variable] | None = None,
        name: str | None = None,
        **kwargs,
    ):
        from pylogic.structures.sequence import FiniteSequence

        latex_str = kwargs.pop("latex_str", None) or r"\cup".join(
            map(lambda x: x._latex(), sets)
        )

        Set.__init__(self, name=name or f"FiniteUnion({','.join(map(str, sets))})", latex_str=latex_str, **kwargs)  # type: ignore
        self.sets: set[Set | Variable] = set(sets) if sets else set()
        self.set_sequence = FiniteSequence(self.name + "_sets", initial_terms=sets or [])  # type: ignore
        self.is_union = True

    def __eq__(self, other: FiniteUnion) -> bool:
        if not isinstance(other, FiniteUnion):
            return NotImplemented
        return self.sets == other.sets

    def __hash__(self) -> int:
        sets_ = tuple(sorted(self.sets, key=lambda x: x.name))
        return hash(("FiniteUnion", self.name, sets_))

    def __str__(self) -> str:
        return f"FiniteUnion({self.sets})"

    def __repr__(self) -> str:
        return f"FiniteUnion({self.sets})"


class Intersection(Set):
    """
    Represents the intersection of finitely many or countably-infinitely many sets.
    """

    def __init__(
        self,
        sets: Sequence[Set | Variable],
        name: str | None = None,
        **kwargs,
    ):
        from pylogic.proposition.quantified.forall import ForallInSet
        from pylogic.theories.natural_numbers import Naturals
        from pylogic.variable import Variable

        pred0 = kwargs.pop("predicate", None)

        k = Variable("k")
        pred = lambda x: (
            ForallInSet(k, Naturals, x.is_in(sets[k]))
            if pred0 is None
            else ForallInSet(k, Naturals, x.is_in(sets[k])).and_(pred0(x))
        )
        latex_str = kwargs.pop("latex_str", None) or rf"\bigcap {sets._latex()}"
        super().__init__(name=name, predicate=pred, latex_str=latex_str, **kwargs)
        self.set_sequence: Sequence[Set | Variable] = sets
        self.is_intersection = True

    def __eq__(self, other: Intersection) -> bool:
        if not isinstance(other, Intersection):
            return NotImplemented
        return self.set_sequence == other.set_sequence

    def __hash__(self) -> int:
        return hash(("Intersection", self.name, self.set_sequence))

    def __str__(self) -> str:
        return f"Intersection({self.set_sequence})"

    def __repr__(self) -> str:
        return f"Intersection({self.set_sequence!r})"


class FiniteIntersection(Intersection):
    """
    Represents an intersection of a specified number of sets.
    """

    @overload
    def __new__(cls) -> Set: ...
    @overload
    def __new__(
        cls, sets: Iterable[Set | Variable], name: str | None = None
    ) -> FiniteIntersection: ...
    def __new__(
        cls,
        sets: Iterable[Set | Variable] | None = None,
        name: str | None = None,
        **kwargs,
    ) -> FiniteIntersection | Set:
        if not sets:
            return UniversalSet
        return object.__new__(cls)

    def __init__(
        self,
        sets: Iterable[Set | Variable] | None = None,
        name: str | None = None,
        **kwargs,
    ):
        from pylogic.structures.sequence import FiniteSequence

        latex_str = kwargs.pop("latex_str", None) or r"\cap".join(
            map(lambda x: x._latex(), sets)
        )

        Set.__init__(self, name=name or f"FiniteIntersection({','.join(map(str, sets))})", latex_str=latex_str, **kwargs)  # type: ignore
        self.sets: set[Set | Variable] = set(sets) if sets else set()
        self.set_sequence = FiniteSequence(self.name + "_sets", initial_terms=sets or [])  # type: ignore
        self.is_intersection = True

    def __eq__(self, other: FiniteIntersection) -> bool:
        if not isinstance(other, FiniteIntersection):
            return NotImplemented
        return self.sets == other.sets

    def __hash__(self) -> int:
        sets_ = tuple(sorted(self.sets, key=lambda x: x.name))
        return hash(("FiniteIntersection", self.name, sets_))

    def __str__(self) -> str:
        return f"FiniteIntersection({self.sets})"

    def __repr__(self) -> str:
        return f"FiniteIntersection({self.sets})"


class CartesProduct(Set):
    """
    Represents the cartesian product of finitely many or countably-infinitely many sets.
    """

    def __init__(
        self,
        sets: Sequence[Set | Variable],
        name: str | None = None,
        **kwargs,
    ):
        latex_str = kwargs.pop("latex_str", None) or rf"\prod {sets._latex()}"
        # pred = kwargs.pop("predicate", None)
        super().__init__(name=name, latex_str=latex_str, **kwargs)
        self.set_sequence: Sequence[Set | Variable] = sets
        self.is_cartes_product = True

    def __eq__(self, other: CartesProduct) -> bool:
        if not isinstance(other, CartesProduct):
            return NotImplemented
        return self.set_sequence == other.set_sequence

    def __hash__(self) -> int:
        return hash(("CartesProduct", self.name, self.set_sequence))

    def __str__(self) -> str:
        return f"CartesProduct({self.set_sequence})"

    def __repr__(self) -> str:
        return f"CartesProduct({self.set_sequence!r})"


class FiniteCartesProduct(CartesProduct):
    """
    Represents a cartesian product of a specified number of sets.
    """

    @overload
    def __new__(cls) -> Set: ...
    @overload
    def __new__(
        cls,
        sets: tuple[Set | Variable, ...] | list[Set | Variable],
        name: str | None = None,
    ) -> FiniteCartesProduct: ...
    def __new__(
        cls,
        sets: tuple[Set | Variable, ...] | list[Set | Variable] | None = None,
        name: str | None = None,
        **kwargs,
    ) -> FiniteCartesProduct | Set:
        if not sets:
            return SingletonEmpty
        return object.__new__(cls)

    def __init__(
        self,
        sets: tuple[Set | Variable, ...] | list[Set | Variable] | None = None,
        name: str | None = None,
        **kwargs,
    ):
        from pylogic.structures.sequence import FiniteSequence

        latex_str = kwargs.pop("latex_str", None) or r"\times".join(
            map(lambda x: x._latex(), sets)
        )

        Set.__init__(self, name=name or f"FiniteCartesProduct({','.join(map(str, sets))})", latex_str=latex_str, **kwargs)  # type: ignore
        self.sets: set[Set | Variable] = set(sets) if sets else set()
        self.set_tuple: tuple[Set | Variable, ...] = tuple(sets) if sets else tuple()
        self.set_sequence = FiniteSequence(self.name + "_sets", initial_terms=sets or [])  # type: ignore
        self.is_cartes_product = True

    def __eq__(self, other: FiniteCartesProduct) -> bool:
        if not isinstance(other, FiniteCartesProduct):
            return NotImplemented
        return self.sets == other.sets

    def __hash__(self) -> int:
        sets_ = tuple(sorted(self.sets, key=lambda x: x.name))
        return hash(("FiniteCartesProduct", self.name, sets_))

    def __str__(self) -> str:
        return f"FiniteCartesProduct({self.sets})"


class CartesPower(Set):
    """
    Represents the cartesian power of a set, such as R^2 = R x R.
    """

    # TODO: rules
    # note that * is left-associative (left to right)
    """
    UniversalSet * A = UniversalSet
    EmptySet * A = EmptySet
    SingletonEmpty * A = A
    """

    def __init__(
        self,
        base_set: Set | Variable,
        power: Term,
        name: str | None = None,
        **kwargs,
    ):
        latex_str = (
            kwargs.pop("latex_str", None)
            or rf"{{{base_set._latex()}}}^{{{power._latex()}}}"
        )
        super().__init__(name=name, latex_str=latex_str, **kwargs)
        self.base_set: Set | Variable = base_set
        self.power: Term = power  # TODO: check that power is natural number, int, etc.
        self.is_cartes_power = True

    def __eq__(self, other: CartesPower) -> bool:
        if not isinstance(other, CartesPower):
            return NotImplemented
        return self.base_set == other.base_set and self.power == other.power

    def __hash__(self) -> int:
        return hash(("CartesPower", self.base_set, self.power))

    def __str__(self) -> str:
        power = self.power if isinstance(self.power, Symbol) else f"({self.power})"
        return f"{self.base_set}^{power}"

    def __repr__(self) -> str:
        return f"CartesPower({self.base_set!r}, {self.power!r})"


class Complement(Set):
    """
    Represents the complement of a set.
    """

    def __init__(
        self,
        base_set: Set | Variable,
        name: str | None = None,
        **kwargs,
    ):
        latex_str = kwargs.pop("latex_str", None) or rf"{base_set._latex()}^{{c}}"
        super().__init__(name=name, latex_str=latex_str, **kwargs)
        self.base_set: Set | Variable = base_set


class Difference(Set):
    r"""
    Represents the difference of two sets A \ B = A n B^c.
    """

    def __init__(
        self,
        a: Set | Variable,
        b: Set | Variable,
        name: str | None = None,
        **kwargs,
    ):
        latex_str = (
            kwargs.pop("latex_str", None) or rf"{a._latex()} \setminus {b._latex()}"
        )
        super().__init__(name=name, latex_str=latex_str, **kwargs)
        self.a: Set | Variable = a
        self.b: Set | Variable = b

    def __eq__(self, other: Difference) -> bool:
        if not isinstance(other, Difference):
            return NotImplemented
        return self.a == other.a and self.b == other.b

    def __hash__(self) -> int:
        return hash(("Difference", self.a, self.b))

    def __str__(self) -> str:
        return f"{self.a} \\ {self.b}"

    def __repr__(self) -> str:
        return f"Difference({self.a!r}, {self.b!r})"

    def to_intersection(self) -> FiniteIntersection:
        return FiniteIntersection(sets=[self.a, Complement(self.b)])


class SeqSet(Set):
    """
    Represents a set containing all elements of a sequence.
    """

    def __init__(
        self,
        sequence: Sequence | Variable,
        name: str | None = None,
        **kwargs,
    ):
        from pylogic.proposition.quantified.exists import ExistsInSet
        from pylogic.theories.natural_numbers import Naturals
        from pylogic.variable import Variable

        latex_str = (
            kwargs.pop("latex_str", None) or rf"\{{ {sequence._latex()} \cdots \}}"
        )
        pred0 = kwargs.pop("predicate", None)

        k = Variable("k")
        pred = lambda x: (
            ExistsInSet(k, Naturals, x.equals(sequence[k]))
            if pred0 is None
            else ExistsInSet(k, Naturals, x.equals(sequence[k])).and_(pred0(x))
        )
        super().__init__(name=name, predicate=pred, latex_str=latex_str, **kwargs)
        self.sequence: Sequence | Variable = sequence

    def __eq__(self, other: SeqSet) -> bool:
        if not isinstance(other, SeqSet):
            return NotImplemented
        return self.sequence == other.sequence

    def __hash__(self) -> int:
        return hash(("SeqSet", self.sequence))

    def __str__(self) -> str:
        return f"{{{self.sequence}...}}"

    def __repr__(self) -> str:
        return f"SeqSet({self.sequence!r})"
