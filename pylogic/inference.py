from typing import Generic, TypeVar, TypeVarTuple

from pylogic.proposition.proposition import Proposition


class InvalidRuleError(Exception):
    def __init__(self, rule: str) -> None:
        super().__init__(f"Invalid rule: {rule}")


rules: set[str] = {
    "absolute_value_nonnegative_f",
    "all_proven",
    "apply",
    "by_cases",
    "by_containment_func",
    "by_sympy_def",
    "by_definition",
    "by_empty",
    "by_inspection",
    "by_predicate",
    "by_simplification",
    "contradicts",
    "contrapositive",
    "converse",
    "de_morgan",
    "de_nest",
    "definite_clause_resolve",
    "exists_modus_ponens",
    "extract",
    "first_unit_definite_clause_resolve",
    "followed_from",
    "forward_implication",
    "function_application",
    "given",
    "hypothetical_syllogism",
    "impl_elim",
    "in_particular",
    "inverse",
    "is_absolute",
    "is_even_power",
    "is_one_of",
    "is_rational_power",
    "is_special_case_of",
    "left_distribute",
    "modus_ponens",
    "modus_tollens",
    "mul_inverse",
    "multiply_by_negative",
    "multiply_by_number",
    "multiply_by_positive",
    "one_proven",
    "one_proven_rem_false",
    "order_axiom_bf",
    "p_and",
    "p_and_reverse",
    "p_multiply_by_negative",
    "p_multiply_by_positive",
    "p_substitute",
    "p_substitute_into",
    "quantified_modus_ponens",
    "reflexive",
    "resolve",
    "reverse_implication",
    "right_distribute",
    "strong_induction",
    "symmetric",
    "thus_assumptions_cannot_all_hold",
    "thus_contained_in_all",
    "thus_contained_in_at_least_one",
    "thus_forall",
    "thus_forall_in_set",
    "thus_there_exists",
    "to_conjunction",
    "to_disjunction",
    "to_forall",
    "to_greater_than",
    "to_less_than",
    "to_negative_inequality",
    "to_positive_inequality",
    "todo",
    "transitive",
    "unit_resolve",
    "weak_induction",
    "zero_abs_is_0",
}

T = TypeVar("T", bound="Proposition")
Props = TypeVarTuple("Props")


class Inference(Generic[T, *Props]):
    """
    Represents an inference in a proof.

    Raises:
        InvalidRuleError: if the rule is not in the set of valid rules
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
