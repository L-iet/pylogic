from __future__ import annotations

from typing import TypeVar

from pylogic import Term
from pylogic.proposition.ordering.partial import PartialOrder, StrictPartialOrder

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
