from typing import TypeVar

from pylogic.proposition.proposition import Proposition
from pylogic.proposition.quantified.forall import Forall
from pylogic.proposition.quantified.exists import Exists
from pylogic.proposition.and_ import And
from pylogic.proposition.or_ import Or
from pylogic.proposition.implies import Implies

T = TypeVar("T", bound="Proposition")
U = TypeVar("U", bound="Proposition")


def mp_prop(prem: Proposition, premises: list[Proposition], target: Proposition):
    for other in premises:
        if isinstance(other, Implies):
            try:
                new_conc = prem.modus_ponens(other)
            except AssertionError:
                continue
            if new_conc == target:
                return [prem, other, "modus_ponens", new_conc]


def proof_search(premises: list[Proposition], target: Proposition):
    for prem in premises:
        if prem.__class__ == Proposition:
            return mp_prop(prem, premises, target)
