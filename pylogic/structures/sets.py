from __future__ import annotations
from typing import Callable, TYPE_CHECKING

from sympy import Set as SympySet
import sympy as sp

if TYPE_CHECKING:
    from pylogic.symbol import Symbol
    from pylogic.structures.sets import Set
    from pylogic.expressions.expr import Expr
    from pylogic.proposition.relation.contains import IsContainedIn

    Term = Symbol | Set | Expr | int | float


class Set:
    def __init__(
        self,
        name: str | None = None,
        sympy_set: SympySet | None = None,
        containment_function: Callable[[Term], bool] | None = None,
    ):
        if name:
            name = name.strip()
        else:
            name = ""
            assert (
                sympy_set is not None
            ), "Must provide a sympy Set or a name for a new set"
        if sympy_set is None:
            sympy_set = sp.Set(name)
        assert " " not in name, "Set name cannot contain spaces"
        self.name = name or str(sympy_set)
        self.sympy_set = sympy_set
        self.containment_function: Callable[[Term], bool] = containment_function or (
            lambda x: False
        )

    def __eq__(self, other: object) -> bool:
        if isinstance(other, sp.Set):
            return self.sympy_set == other
        elif not isinstance(other, Set):
            return False
        return self.sympy_set == other.sympy_set

    def equals(self, other: Set) -> bool:
        if not isinstance(other, Set):
            return False
        return self.sympy_set == other.sympy_set

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
        return Set(self.name, self.sympy_set, self.containment_function)


Integers = Set(sympy_set=sp.Integers)
Rationals = Set(sympy_set=sp.Rationals)
Reals = Set(sympy_set=sp.Reals)
Naturals = Set(sympy_set=sp.Naturals)
Naturals0 = Set(sympy_set=sp.Naturals0)
Graphs = Set(name="Graphs", containment_function=lambda x: x.is_graph)  # type: ignore
# Matrices = Set(name="Matrices")
# Vectors = Set(name="Vectors")
# Functions = Set(name="Functions")
Sequences = Set(name="Sequences", containment_function=lambda x: x.is_sequence)  # type: ignore
# Lists = Set(name="Lists", containment_function=lambda x: x.is_list) # type: ignore
# Pairs = Set(name="Pairs", containment_function=lambda x: x.is_pair) # type: ignore
