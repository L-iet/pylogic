from typing import TypeVar, Generic, Literal

from pylogic.proposition.proposition import Proposition
from pylogic.proposition.quantified.forall import Forall
from pylogic.proposition.quantified.exists import Exists
from pylogic.proposition.and_ import And
from pylogic.proposition.or_ import Or
from pylogic.proposition.implies import Implies

T = TypeVar("T", bound="Proposition")
U = TypeVar("U", bound="Proposition")
V = TypeVar("V", bound="Proposition")

RuleName = Literal[
    "p_substitute",
    "p_and",
    "p_and_reverse",
    "modus_ponens",
    "is_one_of",
    "is_special_case_of",
    "followed_from",
    "thus_there_exists",
    "thus_forall",
    "hypothetical_syllogism",
    "all_proven",
    "quantified_modus_ponens",
    "hence_matrices_are_equal",
    "exists_modus_ponens",
]


class InferenceResult(Generic[T, U]):
    def __init__(
        self, starting_prem: T, *other_prems: Proposition, rule: RuleName, target: U
    ) -> None:
        self.starting_prem: T = starting_prem
        self.other_prems: tuple[Proposition, ...] = other_prems
        self.rule: RuleName = rule
        self.target: U = target

    def __repr__(self) -> str:
        return f"InfResult{(self.starting_prem, *self.other_prems, self.rule, self.target)}"

    def __str__(self) -> str:
        return str((self.starting_prem, *self.other_prems, self.rule, self.target))


def mp_search(
    prem: T, premises: list[Proposition], target: U
) -> InferenceResult[T, U] | None:
    """
    Search for if target can be inferred from the premises using modus ponens.
    """
    for other in premises:
        if isinstance(other, Implies):
            try:
                new_conc = prem.modus_ponens(other)
            except (AssertionError, AttributeError):
                continue
            if new_conc == target:
                return InferenceResult(prem, other, rule="modus_ponens", target=new_conc)  # type: ignore
    return None


def hs_search(
    prem: Implies[T, U], premises: list[Proposition], target: Implies[T, V]
) -> InferenceResult[Implies[T, U], Implies[T, V]] | None:
    """Search for if target can be inferred from the premises using
    hypothetical syllogism"""
    for other in premises:
        try:
            new_conc = prem.hypothetical_syllogism(other)
        except (AssertionError, AttributeError):
            continue
        if new_conc == target:
            return InferenceResult(prem, other, rule="hypothetical_syllogism", target=new_conc)  # type: ignore
    return None


def proof_search(premises: list[Proposition], target: Proposition):
    for prem in premises:
        if prem.__class__ == Proposition:
            res = mp_search(prem, premises, target)
            if res:
                return res
        elif prem.__class__ == Implies:
            if target.__class__ == Implies:
                res = hs_search(prem, premises, target)
                if res:
                    return res
