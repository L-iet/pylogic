# Lean example on triangle numbers https://ahelwer.ca/post/2020-04-05-lean-assignment/
from __future__ import annotations

import sys
from abc import ABC, abstractmethod
from typing import TYPE_CHECKING, Any, Self

if not sys.warnoptions:
    import warnings

    from pylogic.warn import PylogicInternalWarning

    warnings.simplefilter("ignore", PylogicInternalWarning)

if TYPE_CHECKING:
    from decimal import Decimal
    from fractions import Fraction

    from pylogic.expressions.expr import Expr
    from pylogic.structures.sequence import Sequence
    from pylogic.structures.set_ import Set
    from pylogic.symbol import Symbol
    from pylogic.variable import Variable

    PythonNumeric = Fraction | int | float | complex | Decimal
    PBasic = Symbol | PythonNumeric
    Unevaluated = Symbol | Sequence | Set | Expr
    Term = Unevaluated | PythonNumeric
    Unification = dict[Variable, Term]
else:
    Term = Any
    PythonNumeric = Any
    PBasic = Any
    Unevaluated = Any
    Unification = Any


class PylogicObject(ABC):
    """
    Base class for all pylogic objects.
    """

    @abstractmethod
    def replace(self, **kwargs) -> Self:
        """
        Replace the attributes of the object with the given values.
        """
        ...
