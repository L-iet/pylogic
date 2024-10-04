from __future__ import annotations

from fractions import Fraction
from typing import TYPE_CHECKING, Any, TypeVar

from pylogic import Term
from pylogic.proposition.ordering.ordering import _Ordering
from pylogic.proposition.ordering.partial import PartialOrder, StrictPartialOrder
from pylogic.proposition.relation.binaryrelation import BinaryRelation

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
