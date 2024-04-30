from __future__ import annotations
from pylogic.proposition.proposition import get_assumptions
from pylogic.proposition.relation.binaryrelation import BinaryRelation
from pylogic.proposition.relation.equals import Equals
from pylogic.proposition.ordering.ordering import _Ordering
from typing import TYPE_CHECKING

import sympy as sp
from sympy import S as sympy_S

if TYPE_CHECKING:
    from pylogic.proposition.ordering.lessthan import LessThan
    from pylogic.proposition.not_ import Not
    from pylogic.symbol import Symbol
    from pylogic.structures.sets import Set

    Term = Symbol | Set | sp.Basic | int | float


class GreaterThan(BinaryRelation, _Ordering):
    is_transitive = True
    name = "GreaterThan"
    infix_symbol = ">"
    infix_symbol_latex = ">"

    @staticmethod
    def is_absolute(expr: Term, expr_not_zero: Not[Equals]) -> "GreaterThan":
        """Logical tactic.
        Given an expr of the form sympy.Abs(x) and a proof that the expr is
        not zero,
        return a proven proposition that says sympy.Abs(x) > 0
        """
        from pylogic.inference import Inference

        assert isinstance(expr, sp.Abs), f"{expr} is not an absolute value"
        assert expr_not_zero.is_proven, f"{expr_not_zero} is not proven"
        assert isinstance(
            expr_not_zero.negated, Equals
        ), f"{expr_not_zero} is not a proof that {expr} is not 0"
        assert expr_not_zero.negated.left == expr
        assert expr_not_zero.negated.right == sp.Integer(0)
        return GreaterThan(
            expr,
            0,
            _is_proven=True,
            _inference=Inference(None, expr_not_zero, rule="is_absolute"),
            _assumptions=get_assumptions(expr_not_zero),
        )

    @staticmethod
    def is_even_power(expr: Term) -> "GreaterThan":
        """Logical tactic.
        Given an expr of the form x**(2n), return a proven proposition that says
        x**(2n) > 0
        """
        assert isinstance(expr, sp.Pow), f"{expr} is not a power"
        assert expr.base.is_real, f"{expr.base} is not a real number"
        assert sp.ask(sp.Q.even(expr.exp)), f"{expr} is not a square or even power"
        return GreaterThan(expr, 0, _is_proven=True)

    @staticmethod
    def is_rational_power(
        expr: Term, proof_base_is_positive: "GreaterThan"
    ) -> "GreaterThan":
        """Logical tactic.
        Given an expr of the form x**(p/q) and a proof that x > 0,
        return a proven proposition that says
        x**(p/q) > 0
        """
        from pylogic.inference import Inference

        assert isinstance(expr, sp.Pow), f"{expr} is not a power"
        assert expr.base.is_real, f"{expr.base} is not a real number"
        assert (
            proof_base_is_positive.is_proven
        ), f"{proof_base_is_positive} is not proven"
        assert isinstance(
            proof_base_is_positive, GreaterThan
        ), f"{proof_base_is_positive} is not a GreaterThan"
        assert (
            proof_base_is_positive.left == expr.base
            and proof_base_is_positive.right == 0
        ), f"{proof_base_is_positive} does not say that {expr.base} is positive"
        assert sp.ask(sp.Q.rational(expr.exp)), f"{expr} is not a rational power"
        return GreaterThan(
            expr,
            0,
            _is_proven=True,
            _assumptions=get_assumptions(proof_base_is_positive),
            _inference=Inference(
                None, proof_base_is_positive, rule="is_rational_power"
            ),
        )

    def __init__(
        self,
        left: Term,
        right: Term,
        is_assumption: bool = False,
        description: str = "",
        **kwargs,
    ) -> None:
        diff = left - right
        if isinstance(diff, int) or isinstance(diff, float):
            diff_is_positive = diff > 0
        else:
            diff_is_positive = diff.is_positive
        if diff_is_positive == False and (is_assumption or _is_proven):
            raise ValueError(f"Some assumptions in {left}, {right} are contradictory")
        super().__init__(
            left, right, is_assumption=is_assumption, description=description, **kwargs
        )
        self.left: Term = left
        self.right: Term = right

    def __repr__(self) -> str:
        return f"{self.left} > {self.right}"

    def to_positive_inequality(self):
        """If self is of the form a > b, returns an inequality of the form a - b > 0"""
        return GreaterThan(self.left - self.right, sympy_S.Zero)

    def to_negative_inequality(self):
        """If self is of the form a > b, returns an inequality of the form b - a < 0"""
        from pylogic.proposition.ordering.lessthan import LessThan

        return LessThan(self.right - self.left, sympy_S.Zero)

    def multiply_by_positive(
        self, x: Term, proof_x_is_positive: "GreaterThan | LessThan"
    ) -> "GreaterThan":
        return super()._multiply_by(self, x, proof_x_is_positive, _sign="positive")  # type: ignore

    def multiply_by_negative(
        self, x: Term, proof_x_is_negative: "GreaterThan | LessThan"
    ) -> "GreaterThan":
        return super()._multiply_by(self, x, proof_x_is_negative, _sign="negative")

    def p_multiply_by_positive(
        self, x: Term, proof_x_is_positive: "GreaterThan | LessThan"
    ) -> "GreaterThan":
        """Logical tactic.
        Same as multiply_by_positive, but returns a proven proposition"""
        assert self.is_proven, f"{self} is not proven"
        new_p = self.multiply_by_positive(x, proof_x_is_positive)
        new_p._is_proven = True
        return new_p

    def p_multiply_by_negative(
        self, x: Term, proof_x_is_negative: "GreaterThan | LessThan"
    ) -> "GreaterThan":
        """Logical tactic.
        Same as multiply_by_negative, but returns a proven proposition"""
        assert self.is_proven, f"{self} is not proven"
        new_p = self.multiply_by_negative(x, proof_x_is_negative)
        new_p._is_proven = True
        return new_p

    def mul_inverse(self):
        return GreaterThan(
            1 / self.right, 1 / self.left, is_assumption=self.is_assumption
        )

    def to_less_than(self):
        """If self is of the form a > b, returns an inequality of the form b < a"""
        from pylogic.proposition.ordering.lessthan import LessThan

        return LessThan(self.right, self.left, is_assumption=self.is_assumption)

    def p_to_less_than(self):
        """Logical tactic. Same as to_less_than, but returns a proven proposition"""
        assert self.is_proven, f"{self} is not proven"
        new_p = self.to_less_than()
        new_p._is_proven = True
        return new_p

    def by_inspection(self) -> GreaterThan:
        """
        Logical tactic. Determine if the proposition is true by inspection.
        """
        try:
            if bool(self.left > self.right) is True:
                return GreaterThan(self.left, self.right, _is_proven=True)
            else:
                raise ValueError(
                    f"Cannot prove that {self.left} > {self.right} by inspection"
                )
        except TypeError:  # sympy raises TypeError if it can't determine the ordering
            raise ValueError(
                f"Cannot prove that {self.left} < {self.right} by inspection"
            )

    def __mul__(self, other: Term) -> GreaterThan:
        return super()._mul(self, other)

    def __rmul__(self, other: Term) -> GreaterThan:
        return super()._mul(self, other)
