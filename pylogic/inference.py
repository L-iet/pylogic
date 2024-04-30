from typing import Literal, TypeVar, TypeVarTuple

from pylogic.proposition.proposition import Proposition

RuleName = Literal[
    "given",
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
    "de_morgan",
    "thus_assumptions_cannot_all_hold",
    "contradicts",
    "is_absolute",
    "p_multiply_by_positive",
    "p_multiply_by_negative",
    "transitive",
]

rules: list[RuleName] = [
    "given",
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
    "de_morgan",
    "thus_assumptions_cannot_all_hold",
    "contradicts",
    "is_absolute",
    "p_multiply_by_positive",
    "p_multiply_by_negative",
    "transitive",
]

T = TypeVar("T", bound="Proposition")
Props = TypeVarTuple("Props")


class Inference:
    def __init__(
        self,
        starting_premise: T | None,
        *other_premises: *Props,
        rule: RuleName = "given",
    ) -> None:
        self.starting_premise: T | None = starting_premise
        self.other_premises: tuple[*Props] = other_premises
        self.rule: RuleName = rule  # type:ignore

    def __repr__(self) -> str:
        return f"Inference{(self.rule, self.starting_premise, *self.other_premises)}"

    def __str__(self) -> str:
        return str((self.rule, self.starting_premise, *self.other_premises))
