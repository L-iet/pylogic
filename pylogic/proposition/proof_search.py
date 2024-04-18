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
    "modus_ponens",
    "modus_tollens",
    "is_one_of",
    "is_special_case_of",
    "thus_forall",
    "hypothetical_syllogism",
    "all_proven",
    "one_proven",
    "quantified_modus_ponens",
    "exists_modus_ponens",
    "unit_resolve",
    "definite_clause_resolve",
]

rules: list[RuleName] = [
    "modus_ponens",
    "modus_tollens",
    "is_one_of",
    "is_special_case_of",
    "thus_forall",
    "hypothetical_syllogism",
    "all_proven",
    "one_proven",
    "quantified_modus_ponens",
    "exists_modus_ponens",
    "unit_resolve",
    "definite_clause_resolve",
]


class InferenceResult(Generic[T, U]):
    def __init__(
        self,
        starting_prem: T | InferenceResult | None,
        *other_prems: Proposition | InferenceResult,
        rule: RuleName | Literal["known"],
        conclusion: U,
    ) -> None:
        self.starting_prem: T | InferenceResult | None = starting_prem
        self.other_prems: tuple[Proposition | InferenceResult, ...] = other_prems
        self.rule: RuleName = rule  # type:ignore
        self.conclusion: U = conclusion

    def __repr__(self) -> str:
        return f"InfResult{(self.starting_prem, *self.other_prems, self.rule, self.conclusion)}"

    def __str__(self) -> str:
        return str((self.starting_prem, *self.other_prems, self.rule, self.conclusion))


def get_prop(p: InferenceResult[T, U] | U) -> U:
    if isinstance(p, InferenceResult):
        return p.conclusion
    return p


def inference_rule_search(
    rule: RuleName,
    prem: T | InferenceResult[Proposition, T],
    all_props: list[Proposition | InferenceResult],
    premises: list[Proposition | InferenceResult],
    target: U,
) -> InferenceResult[T, U] | None:
    """
    Search for if target can be inferred from the premises using the inference rule.
    premises: propositions we haven't yet called the tactic on
    props: all proven propositions
    """
    prem_prop = get_prop(prem)
    for other in all_props:
        other_prop: Proposition
        other_prop = get_prop(other)
        try:
            new_conc = getattr(prem_prop, rule)(other_prop)
            if new_conc == prem_prop:
                continue
            inf_res = InferenceResult(prem, other, rule=rule, conclusion=new_conc)
            premises.append(inf_res)
            all_props.append(inf_res)
        except (AssertionError, AttributeError) as e:
            continue
        if new_conc == target:
            return inf_res
    return None


def proof_search_one(premises: list[Proposition], target: Proposition):
    all_inferences: list[Proposition | InferenceResult] = premises  # type: ignore
    usable_props: list[Proposition | InferenceResult] = [
        p for p in premises
    ]  # propositions we can call the tactics on
    res = None
    stmt = None  # will hold the outermost non-forall statement of target
    if isinstance(target, Forall):
        stmt = target
    while isinstance(stmt, Forall):
        stmt = stmt.inner_proposition
    while usable_props:
        prem = usable_props.pop()
        prem_prop = get_prop(prem)
        if target == prem_prop:
            return InferenceResult(prem, rule="known", conclusion=target)
        elif stmt == prem_prop:
            return InferenceResult(prem, rule="thus_forall", conclusion=target)

        if res := inference_rule_search(
            "modus_ponens", prem, all_inferences, usable_props, target
        ):
            return res
        if res := inference_rule_search(
            "modus_tollens", prem, all_inferences, usable_props, target
        ):
            return res
        if isinstance(prem_prop, Implies):
            if isinstance(target, Implies):
                res = inference_rule_search(
                    "hypothetical_syllogism", prem, all_inferences, usable_props, target
                )
            if not res and isinstance(prem_prop.antecedent, And):
                res = inference_rule_search(
                    "definite_clause_resolve",
                    prem,
                    all_inferences,
                    usable_props,
                    target,
                )
        elif isinstance(prem_prop, Or):
            res = inference_rule_search(
                "unit_resolve", prem, all_inferences, usable_props, target
            )
        elif isinstance(prem_prop, Forall):
            res = inference_rule_search(
                "quantified_modus_ponens",
                prem,
                all_inferences,
                usable_props,
                target,
            )
            if not res:
                try:
                    result = target.is_special_case_of(prem_prop)
                    inf_res = InferenceResult(
                        prem, rule="is_special_case_of", conclusion=result
                    )
                    usable_props.append(inf_res)
                    all_inferences.append(inf_res)
                    return inf_res
                except (ValueError, AssertionError):
                    continue
        elif isinstance(prem_prop, Exists):
            if isinstance(target, Exists):
                res = inference_rule_search(
                    "exists_modus_ponens", prem, all_inferences, usable_props, target
                )
        elif isinstance(prem_prop, And):
            try:
                result = target.is_one_of(prem_prop)
                inf_res = InferenceResult(prem, rule="is_one_of", conclusion=result)
                usable_props.append(inf_res)
                all_inferences.append(inf_res)
                return inf_res
            except (ValueError, AssertionError):
                continue

        if res:
            return res
        all_props = [get_prop(p) for p in all_inferences]
        if isinstance(target, And):
            if all((t in all_props for t in target.propositions)):
                return InferenceResult(None, rule="all_proven", conclusion=target)
        elif isinstance(target, Or):
            for t in target.propositions:
                if t in all_props:
                    return InferenceResult(t, rule="one_proven", conclusion=target)


def proof_search(
    premises: list[Proposition], target: T, tries: int = 2
) -> InferenceResult[Proposition, T] | None:
    res = None
    for i in range(tries):
        res = proof_search_one(premises, target)
        if res:
            break
    return res  # type: ignore
