from __future__ import annotations

from typing import TYPE_CHECKING

from pylogic.structures.set_ import UniversalSet

if TYPE_CHECKING:
    from pylogic.structures.set_ import Set
    from pylogic.variable import Variable

universal_set = UniversalSet


def set_universe(universe: Set | Variable) -> None:
    global universal_set
    universal_set = universe


def reset_universe() -> None:
    global universal_set
    universal_set = UniversalSet


def get_universe() -> Set | Variable:
    return universal_set
