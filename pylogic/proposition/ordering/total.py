from __future__ import annotations

from fractions import Fraction
from typing import TYPE_CHECKING, Any, TypeVar

from pylogic.proposition.ordering.ordering import _Ordering
from pylogic.proposition.ordering.partial import PartialOrder, StrictPartialOrder
from pylogic.proposition.relation.binaryrelation import BinaryRelation

if TYPE_CHECKING:
    from pylogic.expressions.expr import Expr
    from pylogic.proposition.or_ import Or
    from pylogic.symbol import Symbol

    Numeric = Fraction | int | float
    PBasic = Symbol | Numeric
    UnevaluatedExpr = Symbol | Expr
    Term = UnevaluatedExpr | Numeric
else:
    Term = Any
T = TypeVar("T", bound=Term)
U = TypeVar("U", bound=Term)


class TotalOrder(PartialOrder[T, U]):
    is_strongly_connected = True
    name = "TotalOrder"
    infix_symbol = "<="
    infix_symbol_latex = r"\leq"


class StrictTotalOrder(StrictPartialOrder[T, U]):
    is_connected = True
    name = "StrictTotalOrder"
    infix_symbol = "<"
    infix_symbol_latex = "<"
