from typing import Literal, TypeVar, TypeVarTuple, Generic

from pylogic.proposition.proposition import Proposition


class InvalidRuleError(Exception):
    def __init__(self, rule: str) -> None:
        super().__init__(f"Invalid rule: {rule}")


rules: set[str] = {
    "given",
    "modus_ponens",
    "modus_tollens",
    "is_one_of",
    "is_special_case_of",
    "thus_forall",
    "thus_there_exists",
    "hypothetical_syllogism",
    "all_proven",
    "one_proven",
    "quantified_modus_ponens",
    "exists_modus_ponens",
    "unit_resolve",
    "followed_from",
    "definite_clause_resolve",
    "de_morgan",
    "thus_assumptions_cannot_all_hold",
    "contradicts",
    "is_absolute",
    "p_multiply_by_positive",
    "p_multiply_by_negative",
    "transitive",
    "impl_elim",
    "to_positive_inequality",
    "to_negative_inequality",
    "multiply_by_positive",
    "multiply_by_negative",
    "mul_inverse",
    "to_less_than",
    "by_inspection",
    "to_greater_than",
    "multiply_by_number",
    "is_rational_power",
    "is_even_power",
    "in_particular",
    "by_containment_func",
    "by_def",
    "by_simplification",
    "p_substitute_into",
    "p_substitute",
    "p_and",
    "p_and_reverse",
    "zero_abs_is_0",
    "to_forall",
    "to_disjunction",
    "weak_induction",
    "strong_induction",
    "order_axiom_bf",
    "absolute_value_nonnegative_f",
    "resolve",
    "extract",
    "apply",
    "symmetric",
}

T = TypeVar("T", bound="Proposition")
Props = TypeVarTuple("Props")


class Inference(Generic[T, *Props]):
    """
    Represents an inference in a proof.

    Raises:
        InvalidRuleError: [description] if the rule is not in the set of valid rules
    """

    def __init__(
        self,
        starting_premise: T | None,
        *other_premises: *Props,
        rule: str = "given",
    ) -> None:
        if rule not in rules:
            raise InvalidRuleError(rule)
        self.starting_premise: T | None = starting_premise
        self.other_premises: tuple[*Props] = other_premises
        self.rule: str = rule  # type:ignore

    def __repr__(self) -> str:
        return f"Inference{(self.rule, self.starting_premise, *self.other_premises)}"

    def __str__(self) -> str:
        return str((self.rule, self.starting_premise, *self.other_premises))
