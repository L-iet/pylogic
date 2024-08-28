from __future__ import annotations

from typing import TYPE_CHECKING, Callable, Iterable

import sympy as sp
from sympy import Set as SympySet

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
    Term = Unevaluated | Numeric | sp.Basic


class Set:
    """
    A set S is a collection of elements.
    You can prove the proposition `x in S` either using the containment_function,
    i.e. `S.containment_function(x) == True` using `S.contains(x).by_def()`, or
    by supplying a proven proposition of `S.predicate(x)`.

    S is the set of all x such that `S.predicate(x)` is a true proposition.
    That is, `S.predicate(x) -> x in S`.
    """

    def __init__(
        self,
        name: str,
        elements: Iterable[Term] | None = None,
        containment_function: Callable[[Term], bool] | None = None,
        predicate: Callable[[Term], Proposition] | None = None,
    ):
        name = name.strip()
        sympy_set = sp.Set(name)
        assert " " not in name, "Set name cannot contain spaces"
        self.name = name or str(sympy_set)
        self.sympy_set = sympy_set
        self.elements: set[Term] = set(elements) if elements else set()
        self._containment_function: Callable[[Term], bool] = containment_function or (
            lambda x: x in self.elements
        )
        self.predicate: Callable[[Term], Proposition] | None = predicate

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

    def equals(self, other: Set, **kwargs) -> Equals:
        from pylogic.proposition.relation.equals import Equals

        return Equals(self, other, **kwargs)

    def dummy_eq(self, other: object) -> bool:
        if not isinstance(other, Set):
            return False
        return self.sympy_set == other.sympy_set

    def contains(
        self, other: Term, is_assumption: bool = False, **kwargs
    ) -> IsContainedIn:
        from pylogic.proposition.relation.contains import IsContainedIn

        """elementhood"""

        return IsContainedIn(other, self, is_assumption=is_assumption, **kwargs)

    def evaluate(self) -> sp.Set:
        return self.sympy_set

    def containment_function(self, x: Term) -> bool:
        return self._containment_function(x)

    def __repr__(self) -> str:
        return self.name

    def __copy__(self) -> "Set":
        return self.copy()

    def __hash__(self) -> int:
        return hash((self.name, self.sympy_set, self.containment_function))

    def _latex(self, printer=None) -> str:
        return rf"\text{{{self.name}}}"

    def _repr_latex_(self) -> str:
        return f"$${self._latex()}$$"

    def copy(self) -> Set:
        return Set(self.name, self.elements, self.containment_function)


# Integers = Set(sympy_set=sp.Integers)
# Rationals = Set(sympy_set=sp.Rationals)
# Reals = Set(sympy_set=sp.Reals)
# Naturals = Set(sympy_set=sp.Naturals)
# Naturals0 = Set(sympy_set=sp.Naturals0)
# Graphs = Set(name="Graphs", containment_function=lambda x: x.is_graph)  # type: ignore
# Matrices = Set(name="Matrices")
# Vectors = Set(name="Vectors")
# Functions = Set(name="Functions")
Sequences = Set(name="Sequences", containment_function=lambda x: x.is_sequence)  # type: ignore
# Lists = Set(name="Lists", containment_function=lambda x: x.is_list) # type: ignore
# Pairs = Set(name="Pairs", containment_function=lambda x: x.is_pair) # type: ignore

x = sp.Symbol("x")
