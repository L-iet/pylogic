from __future__ import annotations

from fractions import Fraction
from typing import TYPE_CHECKING, TypeVar

import sympy as sp

from pylogic.expressions.expr import Expr, distance, to_sympy
from pylogic.proposition.quantified.exists import ExistsInSet
from pylogic.proposition.quantified.forall import ForallInSet
from pylogic.typing import Term
from pylogic.variable import Variable

if TYPE_CHECKING:
    from pylogic.constant import Constant
    from pylogic.proposition.implies import Implies
    from pylogic.proposition.ordering.greaterorequal import GreaterOrEqual
    from pylogic.proposition.ordering.greaterthan import GreaterThan
    from pylogic.proposition.ordering.lessthan import LessThan
    from pylogic.structures.sequence import Sequence


class Limit(Expr):
    # order of operations for expressions (0-indexed)
    # Function MinElement/Limit Abs SequenceTerm Pow Prod Mul Sum Add Binary_Expr
    # Custom_Expr Piecewise Relation(eg <, subset)
    _precedence = 1

    _is_wrapped = True

    @classmethod
    def make_epsilon_N_definition(
        cls, limit: Term, sequence: Sequence | Variable, **kwargs
    ) -> ForallInSet:
        from pylogic.proposition.ordering.greaterorequal import GreaterOrEqual
        from pylogic.proposition.ordering.greaterthan import GreaterThan
        from pylogic.proposition.ordering.lessthan import LessThan
        from pylogic.theories.natural_numbers import Naturals
        from pylogic.theories.real_numbers import Reals

        eps = Variable("\\epsilon", latex_name="\\epsilon")
        N = Variable("N")
        n = Variable("n")
        inner_prop = GreaterThan(eps, 0).implies(
            ExistsInSet(
                N,
                Naturals,
                ForallInSet(
                    n,
                    Naturals,
                    GreaterOrEqual(n, N).implies(
                        LessThan(distance(sequence[n], limit), eps)
                    ),
                ),
            )
        )
        return ForallInSet(
            eps,
            Reals,
            inner_prop,
            **kwargs,
        )

    def __init__(self, *args, **kwargs) -> None:
        super().__init__(*args, **kwargs)
        self.mutable_attrs_to_copy = self.mutable_attrs_to_copy + [
            "sequence",
            "epsilon_N_definition",
        ]

    def __new_init__(self, sequence: Sequence | Variable) -> None:
        super().__new_init__(sequence)
        from pylogic.inference import Inference

        self.sequence: Sequence | Variable = sequence

        self.epsilon_N_definition = Limit.make_epsilon_N_definition(
            self,
            sequence,
            _is_proven=True,
            _assumptions=set(),
            _inference=Inference(None, rule="by_definition"),
        )
        self.knowledge_base.add(self.epsilon_N_definition)

    def evaluate(self, **kwargs) -> Limit | Constant:
        n = Variable("n")
        n_sympy = n.to_sympy()
        if self.sequence.nth_term is not None:
            return sp.limit(self.sequence.nth_term(n).to_sympy(), n_sympy, sp.oo)
        return self

    def _latex(self) -> str:
        return f"\\lim {self.sequence._latex()}"

    def __str__(self) -> str:
        return f"Limit({self.sequence})"

    def update_properties(self) -> None:
        return
