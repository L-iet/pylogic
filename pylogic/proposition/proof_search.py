from __future__ import annotations
from typing import TypeVar, Generic, Literal

from pylogic.proposition.proposition import Proposition
from pylogic.proposition.quantified.forall import Forall
from pylogic.proposition.quantified.quantified import _Quantified
from pylogic.proposition.quantified.exists import Exists
from pylogic.proposition.and_ import And
from pylogic.proposition.or_ import Or
from pylogic.proposition.implies import Implies

T = TypeVar("T", bound="Proposition")
U = TypeVar("U", bound="Proposition")
V = TypeVar("V", bound="Proposition")

RuleName = Literal[
    "p_substitute",
    "modus_ponens",
    "is_one_of",
    "is_special_case_of",
    "thus_forall",
    "hypothetical_syllogism",
    "all_proven",
    "quantified_modus_ponens",
    "exists_modus_ponens",
]

rules: list[RuleName] = [
    "p_substitute",
    "modus_ponens",
    "is_one_of",
    "is_special_case_of",
    "thus_forall",
    "hypothetical_syllogism",
    "all_proven",
    "quantified_modus_ponens",
    "exists_modus_ponens",
]


class InferenceResult(Generic[T, U]):
    def __init__(
        self,
        starting_prem: T | InferenceResult,
        *other_prems: Proposition | InferenceResult,
        rule: RuleName,
        conclusion: U,
    ) -> None:
        self.starting_prem: T | InferenceResult = starting_prem
        self.other_prems: tuple[Proposition | InferenceResult, ...] = other_prems
        self.rule: RuleName = rule
        self.conclusion: U = conclusion

    def __repr__(self) -> str:
        return f"InfResult{(self.starting_prem, *self.other_prems, self.rule, self.conclusion)}"

    def __str__(self) -> str:
        return str((self.starting_prem, *self.other_prems, self.rule, self.conclusion))


def get_prop(p: InferenceResult[T, U] | U) -> U:
    if isinstance(p, InferenceResult):
        return p.conclusion
    return p


def mp_search(
    prem: T | InferenceResult[Proposition, T],
    all_props: list[Proposition | InferenceResult],
    premises: list[Proposition | InferenceResult],
    target: U,
) -> InferenceResult[T, U] | None:
    """
    Search for if target can be inferred from the premises using modus ponens.
    premises: propositions we haven't yet called the tactic on
    props: all proven propositions
    """
    prem_prop = get_prop(prem)
    for other in all_props:
        other_prop: Proposition
        other_prop = get_prop(other)
        if isinstance(other_prop, Implies):
            try:
                new_conc = prem_prop.modus_ponens(other_prop)
                inf_res = InferenceResult(
                    prem, other, rule="modus_ponens", conclusion=new_conc
                )
                premises.append(inf_res)
                all_props.append(inf_res)
            except (AssertionError, AttributeError):
                continue
            if new_conc == target:
                return inf_res
    return None


def hs_search(
    prem: Implies[T, U] | InferenceResult[Proposition, Implies[T, U]],
    all_props: list[Proposition | InferenceResult],
    premises: list[Proposition | InferenceResult],
    target: Implies[T, V],
) -> InferenceResult[Implies[T, U], Implies[T, V]] | None:
    """Search for if target can be inferred from the premises using
    hypothetical syllogism"""
    prem_prop = get_prop(prem)
    for other in all_props:
        other_prop = get_prop(other)
        try:
            new_conc = prem_prop.hypothetical_syllogism(other_prop)  # type: ignore
            inf_res = InferenceResult(
                prem, other, rule="hypothetical_syllogism", conclusion=new_conc
            )
            premises.append(inf_res)
            all_props.append(inf_res)
        except (AssertionError, AttributeError):
            continue
        if new_conc == target:
            return inf_res
    return None


def qmp_search(
    prem: Forall[T] | InferenceResult[Proposition, Forall[T]],
    all_props: list[Proposition | InferenceResult],
    premises: list[Proposition | InferenceResult],
    target: Forall[U] | Exists[U],
) -> InferenceResult[Forall[T], Forall[U] | Exists[U]] | None:
    """Search for rule Quantified modus ponens"""
    prem_prop = get_prop(prem)
    for other in all_props:
        other_prop = get_prop(other)
        try:
            new_conc: _Quantified[U] = prem_prop.quantified_modus_ponens(other_prop)  # type: ignore
            inf_res = InferenceResult(
                prem, other, rule="quantified_modus_ponens", conclusion=new_conc
            )
            premises.append(inf_res)
            all_props.append(inf_res)
        except (AssertionError, AttributeError):
            continue
        if new_conc == target:
            return inf_res
    return None


def proof_search(premises: list[Proposition], target: Proposition):
    all_props: list[Proposition | InferenceResult] = premises
    usable_props: list[Proposition | InferenceResult] = [
        p.copy() for p in premises
    ]  # propositions we can call the tactics on
    res = None
    while usable_props:
        prem = usable_props.pop()
        prem_prop = get_prop(prem)
        res = mp_search(prem, all_props, usable_props, target)
        if isinstance(prem_prop, Implies):
            if isinstance(target, Implies):
                res = hs_search(prem, all_props, usable_props, target)
        elif isinstance(prem_prop, Forall):
            if isinstance(target, _Quantified):
                res = qmp_search(prem, all_props, usable_props, target)  # type: ignore
        if res:
            return res
