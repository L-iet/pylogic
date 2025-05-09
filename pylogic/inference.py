from __future__ import annotations

from typing import TYPE_CHECKING, Generic, TypeVar, TypeVarTuple

from pylogic.proposition.proposition import Proposition

if TYPE_CHECKING:
    from pylogic.assumptions_context import AssumptionsContext


class InvalidRuleError(Exception):
    def __init__(self, rule: str) -> None:
        super().__init__(f"Invalid rule: {rule}")


rules: set[str] = {
    "__add__",
    "__mul__",
    "__neg__",
    "__pow__",
    "__truediv__",
    "absolute_value_nonnegative_f",
    "add_inequalities",
    "add_nonnegative_to_left",
    "add_nonpositive_to_right",
    "add_positive_to_left",
    "all_proven",
    "apply",
    "by_cases",
    "by_containment_func",
    "by_definition",
    "by_empty",
    "by_inspection",
    "by_predicate",
    "by_simplification",
    "by_single_substitution",
    "by_substitution",
    "contradicts",
    "contrapositive",
    "converse",
    "de_morgan",
    "de_nest",
    "definite_clause_resolve",
    "evaluate",
    "ex_falso",
    "exists_modus_ponens",
    "extract",
    "extract_conjuncts",
    "first_unit_definite_clause_resolve",
    "followed_from",
    "forall_modus_ponens",
    "forward_implication",
    "function_application",
    "given",
    "hypothetical_syllogism",
    "impl_elim",
    "impl_to_or",
    "in_particular",
    "inverse",
    "invert_inequality",
    "is_absolute",
    "is_even_power",
    "is_one_of",
    "is_rational_power",
    "is_special_case_of",
    "left_distribute",
    "left_weakening",
    "modus_ponens",
    "modus_tollens",
    "mul_inverse",
    "multiply_by_negative",
    "multiply_by_number",
    "multiply_by_positive",
    "neq_any_thus_not_in_sequence",
    "neq_any_thus_not_in_set",
    "one_proven",
    "one_proven_rem_false",
    "order_axiom_bf",
    "p_and",
    "p_and_reverse",
    "p_multiply_by_negative",
    "p_multiply_by_positive",
    "p_substitute",
    "p_substitute_into",
    "reflexive",
    "rename_variable",
    "resolve",
    "reverse_implication",
    "right_distribute",
    "strong_induction",
    "symmetric",
    "tautology",
    "thus_assumptions_cannot_all_hold",
    "thus_contained_in_all",
    "thus_contained_in_b",
    "thus_contained_in_at_least_one",
    "thus_forall",
    "thus_not_empty",
    "thus_predicate",
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
    "vacuous_implies",
    "weak_induction",
    "zero_abs_is_0",
    "close_assumptions_context",
}


class Inference:
    """
    Represents an inference in a proof.

    Raises:
        InvalidRuleError: if the rule is not in the set of valid rules
    """

    def __init__(
        self,
        starting_premise: Proposition | None,
        *other_premises: Proposition,
        conclusion: Proposition | None = None,
        rule: str = "given",
        inner_contexts: list[AssumptionsContext] | None = None,
    ) -> None:
        # Note: premises and conclusion can be unproven propositions
        # happens for props that were proven within a context
        if rule not in rules:
            raise InvalidRuleError(rule)
        self.starting_premise: Proposition | None = starting_premise
        self.other_premises: tuple[Proposition, ...] = other_premises
        self.premises: tuple[Proposition, ...]
        if starting_premise is not None:
            self.premises = (starting_premise,) + self.other_premises
        else:
            self.premises = self.other_premises
        self.conclusion: Proposition | None = conclusion
        self.rule: str = rule  # type:ignore
        self.inner_contexts: list[AssumptionsContext] = inner_contexts or []

    def __repr__(self) -> str:
        has_inner_contexts = len(self.inner_contexts) > 0
        if has_inner_contexts:
            return f"Inference{(self.rule, *self.premises,'has inner contexts')}"
        return f"Inference{(self.rule, *self.premises)}"

    def __str__(self) -> str:
        has_inner_contexts = len(self.inner_contexts) > 0
        if has_inner_contexts:
            return str((self.rule, *self.premises, "has inner contexts"))
        return str((self.rule, *self.premises))
