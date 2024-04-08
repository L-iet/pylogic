from __future__ import annotations
from sympy import Set as SympySet
from sympy.printing.latex import LatexPrinter
import sympy as sp
from pylogic.proposition.relation.contains import IsContainedIn
from typing import Callable

SympyExpression = sp.Basic | int | float


latex_printer = LatexPrinter()


class Set:
    _is_arbitrary: bool = True

    @property
    def is_arbitrary(self) -> bool:
        return self._is_arbitrary

    def __init__(
        self,
        sympy_set: SympySet | None = None,
        name: str | None = None,
        containment_function: Callable[[SympyExpression | Set], bool] | None = None,
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
        self.containment_function = containment_function or (lambda x: False)

    # def __eq__(self, other: "ArgValueTypes") -> bool:
    #     return self.sympy_set == other.sympy_set

    def equals(self, other: object) -> bool:
        if not isinstance(other, Set):
            return False
        return self.sympy_set == other.sympy_set

    def dummy_eq(self, other: object) -> bool:
        if not isinstance(other, Set):
            return False
        return self.sympy_set == other.sympy_set

    def contains(
        self, other: "SympyExpression | Set", is_assumption: bool = False
    ) -> IsContainedIn:
        """elementhood"""

        return IsContainedIn(other, self, is_assumption=is_assumption)

    def __repr__(self) -> str:
        return self.name

    def __copy__(self) -> "Set":
        return self.copy()

    def _latex(self, printer=latex_printer) -> str:
        return self.name

    def _repr_latex_(self) -> str:
        return f"$${self._latex()}$$"

    def copy(self) -> "Set":
        return Set(self.sympy_set, self.name)
