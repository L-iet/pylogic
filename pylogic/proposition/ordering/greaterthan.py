from __future__ import annotations

from fractions import Fraction
from typing import TYPE_CHECKING, Any, Generic, Self, TypeVar

import sympy as sp
from sympy import S as sympy_S

from pylogic.constant import Constant
from pylogic.expressions.abs import Abs
from pylogic.expressions.expr import Pow
from pylogic.proposition.ordering.ordering import _Ordering
from pylogic.proposition.ordering.total import StrictTotalOrder
from pylogic.proposition.proposition import get_assumptions
from pylogic.proposition.relation.binaryrelation import BinaryRelation
from pylogic.proposition.relation.equals import Equals

if TYPE_CHECKING:
    from pylogic.expressions.expr import Expr
    from pylogic.proposition.not_ import Not
    from pylogic.proposition.ordering.lessthan import LessThan
    from pylogic.symbol import Symbol

    Numeric = Fraction | int | float
    PBasic = Symbol | Numeric
    UnevaluatedExpr = Symbol | Expr
    Term = UnevaluatedExpr | Numeric
else:
    Term = Any
T = TypeVar("T", bound=Term)
U = TypeVar("U", bound=Term)


class GreaterThan(StrictTotalOrder[T, U], _Ordering):
    name = "GreaterThan"
    infix_symbol = ">"
    infix_symbol_latex = ">"

    def __init__(
        self,
        left: T,
        right: U,
        is_assumption: bool = False,
        description: str = "",
        name=None,
        **kwargs,
    ) -> None:
        super().__init__(
            left,
            right,
            name="GreaterThan",
            is_assumption=is_assumption,
            description=description,
            **kwargs,
        )

    def __repr__(self) -> str:
        return f"{self.left} > {self.right}"

    def to_positive_inequality(self):
        """If self is of the form a > b, returns an inequality of the form a - b > 0"""
        from pylogic.inference import Inference

        return GreaterThan(
            self.left - self.right,
            Constant(0),
            _is_proven=self.is_proven,
            _assumptions=get_assumptions(self),
            _inference=Inference(self, rule="to_positive_inequality"),
        )

    def to_negative_inequality(self):
        """If self is of the form a > b, returns an inequality of the form b - a < 0"""
        from pylogic.inference import Inference
        from pylogic.proposition.ordering.lessthan import LessThan

        return LessThan(
            self.right - self.left,
            sympy_S.Zero,
            _is_proven=self.is_proven,
            _assumptions=get_assumptions(self),
            _inference=Inference(self, rule="to_negative_inequality"),
        )

    def multiply_by_positive(
        self, x: Term, proof_x_is_positive: "GreaterThan | LessThan"
    ) -> "GreaterThan":
        from pylogic.inference import Inference

        return super()._multiply_by(
            self,
            x,
            proof_x_is_positive,
            _sign="positive",
            _is_proven=self.is_proven,
            _assumptions=get_assumptions(self).union(
                get_assumptions(proof_x_is_positive)
            ),
            _inference=Inference(
                self, proof_x_is_positive, rule="multiply_by_positive"
            ),
        )

    def multiply_by_negative(
        self, x: Term, proof_x_is_negative: "GreaterThan | LessThan"
    ) -> "GreaterThan":
        from pylogic.inference import Inference

        return super()._multiply_by(
            self,
            x,
            proof_x_is_negative,
            _sign="negative",
            _is_proven=self.is_proven,
            _assumptions=get_assumptions(self).union(
                get_assumptions(proof_x_is_negative)
            ),
            _inference=Inference(
                self, proof_x_is_negative, rule="multiply_by_negative"
            ),
        )

    def p_multiply_by_positive(
        self, x: Term, proof_x_is_positive: "GreaterThan | LessThan"
    ) -> "GreaterThan":
        """Logical tactic.
        Same as multiply_by_positive, but returns a proven proposition"""
        assert self.is_proven, f"{self} is not proven"
        new_p = self.multiply_by_positive(x, proof_x_is_positive)
        return new_p

    def p_multiply_by_negative(
        self, x: Term, proof_x_is_negative: "GreaterThan | LessThan"
    ) -> "GreaterThan":
        """Logical tactic.
        Same as multiply_by_negative, but returns a proven proposition"""
        assert self.is_proven, f"{self} is not proven"
        new_p = self.multiply_by_negative(x, proof_x_is_negative)
        return new_p

    def mul_inverse(self):
        from pylogic.inference import Inference

        return GreaterThan(
            1 / self.right,
            1 / self.left,
            _is_proven=self.is_proven,
            _assumptions=get_assumptions(self),
            _inference=Inference(self, rule="mul_inverse"),
        )

    def to_less_than(self):
        """If self is of the form a > b, returns an inequality of the form b < a"""
        from pylogic.inference import Inference
        from pylogic.proposition.ordering.lessthan import LessThan

        return LessThan(
            self.right,
            self.left,
            _is_proven=self.is_proven,
            _assumptions=get_assumptions(self),
            _inference=Inference(self, rule="to_less_than"),
        )

    def p_to_less_than(self):
        """Logical tactic. Same as to_less_than, but returns a proven proposition"""
        assert self.is_proven, f"{self} is not proven"
        new_p = self.to_less_than()
        return new_p

    def by_inspection(self) -> Self:
        """
        Logical tactic. Determine if the proposition is true by inspection.
        """
        # TODO: Implement this
        raise NotImplementedError

    def __mul__(self, other: Numeric) -> GreaterThan:
        return super()._mul(self, other)

    def __rmul__(self, other: Numeric) -> GreaterThan:
        return super()._mul(self, other)


def is_absolute(expr: Term, expr_not_zero: Not[Equals]) -> "GreaterThan":
    """Logical tactic.
    Given an expr of the form sympy.Abs(x) and a proof that the expr is
    not zero,
    return a proven proposition that says sympy.Abs(x) > 0
    """
    from pylogic.inference import Inference

    assert isinstance(expr, (sp.Abs, Abs)), f"{expr} is not an absolute value"
    assert expr_not_zero.is_proven, f"{expr_not_zero} is not proven"
    assert isinstance(
        expr_not_zero.negated, Equals
    ), f"{expr_not_zero} is not a proof that {expr} is not 0"
    # print(expr_not_zero.negated.left, expr)
    assert expr_not_zero.negated.left == expr
    assert expr_not_zero.negated.right == sp.Integer(0)
    return GreaterThan(
        expr,
        0,
        _is_proven=True,
        _inference=Inference(None, expr_not_zero, rule="is_absolute"),
        _assumptions=get_assumptions(expr_not_zero),
    )


def is_even_power(expr: Term) -> "GreaterThan":
    """Logical tactic.
    Given an expr of the form x**(2n), return a proven proposition that says
    x**(2n) > 0
    """
    from pylogic.inference import Inference

    assert isinstance(expr, (Pow, sp.Pow)), f"{expr} is not a power"
    assert (
        isinstance(expr.base, (int, float, Fraction)) or expr.base.is_real
    ), f"{expr.base} is not a real number"
    assert sp.ask(sp.Q.even(expr.exp)), f"{expr} is not a square or even power"
    return GreaterThan(
        expr,
        0,
        _is_proven=True,
        _inference=Inference(None, rule="is_even_power"),
        _assumptions=set(),  # TODO: change this
    )


def is_rational_power(
    expr: Term, proof_base_is_positive: "GreaterThan"
) -> "GreaterThan":
    """Logical tactic.
    Given an expr of the form x**(p/q) and a proof that x > 0,
    return a proven proposition that says
    x**(p/q) > 0
    """
    from pylogic.inference import Inference

    assert isinstance(expr, (sp.Pow, Pow)), f"{expr} is not a power"
    assert (
        isinstance(expr.base, (int, float, Fraction)) or expr.base.is_real
    ), f"{expr.base} is not a real number"
    assert proof_base_is_positive.is_proven, f"{proof_base_is_positive} is not proven"
    assert isinstance(
        proof_base_is_positive, GreaterThan
    ), f"{proof_base_is_positive} is not a GreaterThan"
    assert (
        proof_base_is_positive.left == expr.base and proof_base_is_positive.right == 0
    ), f"{proof_base_is_positive} does not say that {expr.base} is positive"
    assert sp.ask(sp.Q.rational(expr.exp)), f"{expr} is not a rational power"
    return GreaterThan(
        expr,
        0,
        _is_proven=True,
        _assumptions=get_assumptions(proof_base_is_positive),
        _inference=Inference(None, proof_base_is_positive, rule="is_rational_power"),
    )
