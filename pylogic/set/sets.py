from __future__ import annotations
from sympy import Set as SympySet
from sympy.printing.latex import LatexPrinter
import sympy as sp
from pylogic.proposition.relation.contains import Contains

SympyExpression = sp.Basic | int | float


latex_printer = LatexPrinter()


class Set:
    _is_arbitrary: bool = True

    @property
    def is_arbitrary(self) -> bool:
        return self._is_arbitrary

    def __init__(self, sympy_set: SympySet, name: str | None = None):
        if name:
            name = name.strip()
        else:
            name = ""
        assert " " not in name, "Set name cannot contain spaces"
        self.name = name or str(sympy_set)
        self.sympy_set = sympy_set

    # def __eq__(self, other: "ArgValueTypes") -> bool:
    #     return self.sympy_set == other.sympy_set

    def dummy_eq(self, other: "Set") -> bool:
        return self.sympy_set == other.sympy_set

    def contains(
        self, other: "SympyExpression | Set", is_assumption: bool = False
    ) -> Contains:
        """elementhood"""

        return Contains(self, other, is_assumption=is_assumption)

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


ArgTypes = type[Set] | type[SympyExpression]
ArgValueTypes = Set | SympyExpression
