from __future__ import annotations

from typing import TYPE_CHECKING, Annotated, TypeVar, cast

from pylogic.infix.infix import SpecialInfix
from pylogic.proposition.proposition import Proposition

P = TypeVar("P", bound=Proposition)
Q = TypeVar("Q", bound=Proposition)

if TYPE_CHECKING:
    from pylogic.expressions.expr import Expr
    from pylogic.proposition.quantified.forall import Forall, ForallInSet


class ByProvers:
    def __init__(
        self,
        starting_premise: Proposition,
        *provers: Proposition | Expr,
        rule: str = "",
    ) -> None:
        self.starting_premise = starting_premise
        self.provers: tuple[Proposition | Expr, ...] = provers
        self.rule: str = rule

    def __ror__(self, p: P) -> P:
        from pylogic.helpers import find_first

        _, first_not_proven = find_first(
            lambda prover: isinstance(prover, Proposition)
            and prover.is_proven == False,
            self.provers + (self.starting_premise,),
        )
        assert first_not_proven is None, f"{first_not_proven} is not proven"
        if hasattr(self.starting_premise, self.rule):
            return cast(P, getattr(self.starting_premise, self.rule)(*self.provers))
        raise ValueError(f"{self.starting_premise} does not have a method {self.rule}")


def by_call(*ps: Proposition, rule: str = "") -> ByProvers:
    return ByProvers(*ps, rule=rule)


def by_forall(p: P, prover: Forall[Proposition] | ForallInSet[Proposition]) -> P:
    """
    Logical inference rule. We try to prove p using prover, a Forall statement.
    """
    from pylogic.inference import Inference
    from pylogic.proposition.proposition import get_assumptions
    from pylogic.proposition.quantified.forall import Forall, ForallInSet

    # We dig till the firt non-Forall proposition
    layer = prover
    p_type = type(p)
    while isinstance(layer, Forall):
        match layer:
            case ForallInSet():
                layer = layer._inner_without_set
            case Forall():
                layer = layer.inner_proposition

    # If the first non-Forall proposition is not of the same type as p,
    # we cannot prove p using prover
    if type(layer) != p_type:
        raise ValueError(f"Cannot prove {p} using {prover}")
    unification = layer.unify(p)  # type: ignore
    if unification is None:
        raise ValueError(f"Cannot prove {p} using {prover}")
    # this function needs testing to ensure we are
    # not proving fallacies
    new_p = p.copy()
    new_p._set_is_proven(True)
    new_p.deduced_from = Inference(prover, conclusion=new_p, rule="in_particular")
    new_p.from_assumptions = get_assumptions(prover)
    return new_p


def _by(p: P, prover: Proposition) -> P:
    """
    Logical inference rule. We try to prove p using prover.
    """
    assert prover.is_proven, f"{prover} is not proven"
    from pylogic.proposition.quantified.forall import Forall

    if isinstance(prover, Forall):
        return by_forall(p, prover)
    return p


by: Annotated[
    SpecialInfix[Proposition, Proposition, Proposition, ByProvers],
    "Logical inference rule. We try to prove the left argument using the right (prover)",
] = SpecialInfix(_by, by_call)
