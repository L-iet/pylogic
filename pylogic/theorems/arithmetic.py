from __future__ import annotations
from typing import TypeVar, TYPE_CHECKING

from pylogic.proposition.quantified.forall import Forall
from pylogic.proposition.implies import Implies
from pylogic.proposition.and_ import And
from pylogic.proposition.relation.equals import Equals
from pylogic.proposition.relation.contains import IsContainedIn
from pylogic.variable import Variable
from sympy import Add, Integer

if TYPE_CHECKING:
    from pylogic.proposition.proposition import Proposition

    TProposition = TypeVar("TProposition", bound="Proposition")


x = Variable("x", real=True)
y = Variable("y", real=True)
# every number has an additive inverse
x_plus_neg_x = Add(x, -x, evaluate=False)

add_inv = (
    Equals(x_plus_neg_x, Integer(0))
    .by_simplification()
    .thus_there_exists("y", -x)
    .thus_forall(x)
)


def weak_induction(
    base_case: TProposition,
    induction_step: Forall[Implies[And[IsContainedIn, TProposition], TProposition]],
) -> Forall[Implies[IsContainedIn, TProposition]]:
    r"""
    Logical tactic. Induction on the set of natural numbers including 0, `Naturals0`.
    Given base case P(0) and induction step forall n: (n in Naturals0 /\ P(n)) -> P(n+1),
    prove forall n: n in Naturals0 -> P(n).
    """
    from pylogic.structures.sets import Naturals0

    assert base_case.is_proven, f"Base case {base_case} must be proven"
    assert induction_step.is_proven, f"Induction step {induction_step} must be proven"
    assert isinstance(
        induction_step, Forall
    ), f"Induction step {induction_step} must be a forall"
    assert isinstance(
        induction_step.inner_proposition, Implies
    ), f"Statement {induction_step.inner_proposition} must be an implication"
    assert isinstance(
        induction_step.inner_proposition.antecedent, And
    ), f"Antecedent {induction_step.inner_proposition.antecedent} must be a conjunction"
    n = induction_step.variable
    prem1 = induction_step.inner_proposition.antecedent.propositions[0]
    prem2 = induction_step.inner_proposition.antecedent.propositions[1]
    assert (
        prem1.set_ == Naturals0
    ), f"First premise {prem1} must be a statement about Naturals0"
    assert prem1.element == n, f"First premise {prem1} must be a statement about n"
    pred = induction_step.inner_proposition.consequent
    p0 = pred.replace(n, -1)
    assert (
        p0 == base_case == prem2.replace(n, 0)
    ), f"Base case {base_case} must be the same as P(0)"
    return Forall(n, IsContainedIn(n, Naturals0).implies(prem2))
