from __future__ import annotations

import sympy as sp

from pylogic.expressions.expr import Expr
from pylogic.typing import Term


class MaxElement(Expr):
    # order of operations for expressions (0-indexed)
    # Function MinElement Abs SequenceTerm Pow Prod Mul Sum Add Binary_Expr
    # Custom_Expr Piecewise Relation(eg <, subset)
    _precedence = 1
    _is_wrapped = True

    def __init__(self, *args, **kwargs) -> None:
        super().__init__(*args, **kwargs)
        self.mutable_attrs_to_copy = self.mutable_attrs_to_copy + ["expr"]

    def __new_init__(self, expr: Term) -> None:
        super().__new_init__(expr)
        self.expr = self.args[0]

    def evaluate(self, **kwargs) -> MaxElement | Term:
        from pylogic.helpers import getkey
        from pylogic.proposition.not_ import Not
        from pylogic.proposition.relation.subsets import IsSubsetOf
        from pylogic.structures.set_ import EmptySet, Set
        from pylogic.theories.natural_numbers import Naturals
        from pylogic.theories.real_numbers import Interval
        from pylogic.variable import Variable

        # check if it is an interval of reals closed below
        if isinstance(self.expr, Interval) and self.expr.b_inclusive:
            return self.expr.b
        return self

    def _latex(self) -> str:
        return rf"\text{{MaxElement}}\left({self.expr._latex()}\right)"

    def __str__(self) -> str:
        return f"MaxElement({self.expr})"

    def update_properties(self) -> None:
        return


class Max(Expr):
    # order of operations for expressions (0-indexed)
    # Function MinElement Abs SequenceTerm Pow Prod Mul Sum Add Binary_Expr
    # Custom_Expr Piecewise Relation(eg <, subset)
    _precedence = 1
    _is_wrapped = True

    def __init__(self, *args, **kwargs) -> None:
        super().__init__(*args, **kwargs)
        self.mutable_attrs_to_copy = self.mutable_attrs_to_copy + ["a", "b"]

    def __new_init__(self, a: Term, b: Term) -> None:
        super().__new_init__(a, b)
        self.a = self.args[0]
        self.b = self.args[1]

        from pylogic.inference import Inference
        from pylogic.proposition.ordering.greaterorequal import GreaterOrEqual
        from pylogic.proposition.and_ import And

        geq_a = GreaterOrEqual(
            self,
            self.a,
            _is_proven=True,
            _assumptions=set(),
            _inference=Inference(None, rule="by_definition"),
        )
        geq_b = GreaterOrEqual(
            self,
            self.b,
            _is_proven=True,
            _assumptions=set(),
            _inference=Inference(None, rule="by_definition"),
        )
        geq = And(
            geq_a,
            geq_b,
            _is_proven=True,
            _assumptions=set(),
            _inference=Inference(None, rule="by_definition"),
        )
        self.geq = geq
        self.geq_a = geq_a
        self.geq_b = geq_b
        self.knowledge_base.add(self.geq)
        self.knowledge_base.add(self.geq_a)
        self.knowledge_base.add(self.geq_b)

    def update_properties(self) -> None:
        # self.a and self.b might not be set yet
        a = self.args[0]
        b = self.args[1]
        properties = [
            "real",
            "rational",
            "integer",
            "natural",
            "zero",
            "nonpositive",
            "nonnegative",
            "even",
            "odd",
        ]
        for prop in properties:
            if getattr(a, f"is_{prop}", None) and getattr(b, f"is_{prop}", None):
                setattr(self, f"is_{prop}", True)
            elif (
                getattr(a, f"is_{prop}", None) is False
                and getattr(b, f"is_{prop}", None) is False
            ):
                setattr(self, f"is_{prop}", False)

    def evaluate(self, **kwargs) -> Max | Term:
        from pylogic.constant import Constant
        from pylogic.helpers import is_python_real_numeric

        # check if both are constants, and numeric, return bigger
        if isinstance(self.a, Constant) and isinstance(self.b, Constant):
            if is_python_real_numeric(self.a.value, self.b.value):
                return Constant(max(self.a.value, self.b.value))
        # TODO: check if a >= b or b >= a is in kb
        ...

        return self

    def _latex(self) -> str:
        return rf"\text{{Max}}\left({self.a._latex()}, {self.b._latex()}\right)"

    def __str__(self) -> str:
        return f"Max({self.a}, {self.b})"
