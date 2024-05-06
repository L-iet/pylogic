from __future__ import annotations
from pylogic.proposition.proposition import get_assumptions
from pylogic.proposition.relation.binaryrelation import BinaryRelation
from pylogic.proposition.relation.equals import Equals
from pylogic.proposition.ordering.ordering import _Ordering
from pylogic.expressions.abs import Abs
from pylogic.expressions.expr import Pow
from typing import TYPE_CHECKING, Self

import sympy as sp
from sympy import S as sympy_S

if TYPE_CHECKING:
    from pylogic.proposition.ordering.lessthan import LessThan
    from pylogic.proposition.not_ import Not
    from pylogic.symbol import Symbol
    from pylogic.structures.sets import Set
    from pylogic.expressions.expr import Expr

    NumTerm = Symbol | Expr | int | float


class GreaterThan(BinaryRelation, _Ordering):
    is_transitive = True
    name = "GreaterThan"
    infix_symbol = ">"
    infix_symbol_latex = ">"

    def __init__(
        self,
        left: NumTerm,
        right: NumTerm,
        is_assumption: bool = False,
        description: str = "",
        **kwargs,
    ) -> None:
        _is_proven = kwargs.get("_is_proven", False)
        diff = left - right
        if isinstance(diff, int) or isinstance(diff, float):
            diff_is_positive = diff > 0
        else:
            diff_is_positive = True
        if diff_is_positive == False and (is_assumption or _is_proven):
            raise ValueError(f"Some assumptions in {left}, {right} are contradictory")
        super().__init__(
            left, right, is_assumption=is_assumption, description=description, **kwargs
        )
        self.left: NumTerm = left
        self.right: NumTerm = right

    def __repr__(self) -> str:
        return f"{self.left} > {self.right}"

    def to_positive_inequality(self):
        """If self is of the form a > b, returns an inequality of the form a - b > 0"""
        from pylogic.inference import Inference

        return GreaterThan(
            self.left - self.right,
            sympy_S.Zero,
            _is_proven=self.is_proven,
            _assumptions=get_assumptions(self),
            _inference=Inference(self, rule="to_positive_inequality"),
        )

    def to_negative_inequality(self):
        """If self is of the form a > b, returns an inequality of the form b - a < 0"""
        from pylogic.proposition.ordering.lessthan import LessThan
        from pylogic.inference import Inference

        return LessThan(
            self.right - self.left,
            sympy_S.Zero,
            _is_proven=self.is_proven,
            _assumptions=get_assumptions(self),
            _inference=Inference(self, rule="to_negative_inequality"),
        )

    def multiply_by_positive(
        self, x: NumTerm, proof_x_is_positive: "GreaterThan | LessThan"
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
        self, x: NumTerm, proof_x_is_negative: "GreaterThan | LessThan"
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
        self, x: NumTerm, proof_x_is_positive: "GreaterThan | LessThan"
    ) -> "GreaterThan":
        """Logical tactic.
        Same as multiply_by_positive, but returns a proven proposition"""
        assert self.is_proven, f"{self} is not proven"
        new_p = self.multiply_by_positive(x, proof_x_is_positive)
        return new_p

    def p_multiply_by_negative(
        self, x: NumTerm, proof_x_is_negative: "GreaterThan | LessThan"
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
        from pylogic.proposition.ordering.lessthan import LessThan
        from pylogic.inference import Inference

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

    def by_inspection(self) -> GreaterThan:
        """
        Logical tactic. Determine if the proposition is true by inspection.
        """
        from pylogic.inference import Inference

        try:
            if bool(self.left > self.right) is True:
                return GreaterThan(
                    self.left,
                    self.right,
                    _is_proven=True,
                    _assumptions=set(),
                    _inference=Inference(self, rule="by_inspection"),
                )
            else:
                raise ValueError(
                    f"Cannot prove that {self.left} > {self.right} by inspection"
                )
        except TypeError:  # sympy raises TypeError if it can't determine the ordering
            raise ValueError(
                f"Cannot prove that {self.left} < {self.right} by inspection"
            )

    def __mul__(self, other: int | float) -> GreaterThan:
        return super()._mul(self, other)

    def __rmul__(self, other: int | float) -> GreaterThan:
        return super()._mul(self, other)


def is_absolute(expr: NumTerm, expr_not_zero: Not[Equals]) -> "GreaterThan":
    """Logical tactic.
    Given an expr of the form sympy.Abs(x) and a proof that the expr is
    not zero,
    return a proven proposition that says sympy.Abs(x) > 0
    """
    from pylogic.inference import Inference

    assert isinstance(expr, sp.Abs) or isinstance(
        expr, Abs
    ), f"{expr} is not an absolute value"
    assert expr_not_zero.is_proven, f"{expr_not_zero} is not proven"
    assert isinstance(
        expr_not_zero.negated, Equals
    ), f"{expr_not_zero} is not a proof that {expr} is not 0"
    print(expr_not_zero.negated.left, expr)
    assert expr_not_zero.negated.left == expr
    assert expr_not_zero.negated.right == sp.Integer(0)
    return GreaterThan(
        expr,
        0,
        _is_proven=True,
        _inference=Inference(None, expr_not_zero, rule="is_absolute"),
        _assumptions=get_assumptions(expr_not_zero),
    )


def is_even_power(expr: NumTerm) -> "GreaterThan":
    """Logical tactic.
    Given an expr of the form x**(2n), return a proven proposition that says
    x**(2n) > 0
    """
    from pylogic.inference import Inference

    assert isinstance(expr, sp.Pow), f"{expr} is not a power"
    assert expr.base.is_real, f"{expr.base} is not a real number"
    assert sp.ask(sp.Q.even(expr.exp)), f"{expr} is not a square or even power"
    return GreaterThan(
        expr,
        0,
        _is_proven=True,
        _inference=Inference(None, rule="is_even_power"),
        _assumptions=set(),  # TODO: change this
    )


def is_rational_power(
    expr: NumTerm, proof_base_is_positive: "GreaterThan"
) -> "GreaterThan":
    """Logical tactic.
    Given an expr of the form x**(p/q) and a proof that x > 0,
    return a proven proposition that says
    x**(p/q) > 0
    """
    from pylogic.inference import Inference

    assert isinstance(expr, sp.Pow) or isinstance(expr, Pow), f"{expr} is not a power"
    assert expr.base.is_real, f"{expr.base} is not a real number"
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
