from __future__ import annotations
from pylogic.proposition.relation.binaryrelation import BinaryRelation
from pylogic.proposition.ordering.ordering import _Ordering
from typing import TYPE_CHECKING
from sympy import Basic
from sympy import S as sympy_S

if TYPE_CHECKING:
    from pylogic.proposition.ordering.greaterthan import GreaterThan
    from pylogic.set.sets import Set
    from pylogic.variable import Variable
    from pylogic.symbol import Symbol

    Term = Variable | Symbol | Set | Basic | int | float


class LessThan(BinaryRelation, _Ordering):
    is_transitive = True
    name = "LessThan"
    infix_symbol = "<"
    infix_symbol_latex = "<"

    def __init__(
        self,
        left: Term,
        right: Term,
        is_assumption: bool = False,
        *,
        _is_proven: bool = False,
    ) -> None:
        name = "LessThan"
        diff = right - left
        if isinstance(diff, int) or isinstance(diff, float):
            diff_is_positive = diff > 0
        else:
            diff_is_positive = diff.is_positive
        if diff_is_positive == False and (is_assumption or _is_proven):
            raise ValueError(f"Some assumptions in {left}, {right} are contradictory")
        super().__init__(
            left,
            right,
            is_assumption=is_assumption,
            _is_proven=_is_proven,
        )

    def to_positive_inequality(self):
        """If self is of the form a < b, returns an inequality of the form b - a > 0"""
        return GreaterThan(self.right - self.left, sympy_S.Zero)

    def to_negative_inequality(self):
        """If self is of the form a < b, returns an inequality of the form a - b < 0"""
        return LessThan(self.left - self.right, sympy_S.Zero)

    def multiply_by_positive(
        self, x: Term, proof_x_is_positive: "GreaterThan | LessThan"
    ) -> "LessThan":
        return super()._multiply_by(self, x, proof_x_is_positive, _sign="positive")  # type: ignore

    def multiply_by_negative(
        self, x: Term, proof_x_is_negative: "GreaterThan | LessThan"
    ) -> "LessThan":
        return super()._multiply_by(self, x, proof_x_is_negative, _sign="negative")

    def p_multiply_by_positive(
        self, x: Term, proof_x_is_positive: "GreaterThan | LessThan"
    ) -> "LessThan":
        """Logical tactic.
        Same as multiply_by_positive, but returns a proven proposition"""
        assert self.is_proven, f"{self} is not proven"
        new_p = self.multiply_by_positive(x, proof_x_is_positive)
        new_p._is_proven = True
        return new_p

    def p_multiply_by_negative(
        self, x: Term, proof_x_is_negative: "GreaterThan | LessThan"
    ) -> "LessThan":
        """Logical tactic.
        Same as multiply_by_negative, but returns a proven proposition"""
        assert self.is_proven, f"{self} is not proven"
        new_p = self.multiply_by_negative(x, proof_x_is_negative)
        new_p._is_proven = True
        return new_p

    def mul_inverse(self):
        return LessThan(1 / self.right, 1 / self.left, is_assumption=self.is_assumption)

    def to_greater_than(self):
        """If self is of the form a < b, returns an inequality of the form b > a"""
        return GreaterThan(self.right, self.left, is_assumption=self.is_assumption)

    def p_to_greater_than(self):
        """Logical tactic. Same as to_greater_than, but returns a proven proposition"""
        assert self.is_proven, f"{self} is not proven"
        new_p = self.to_greater_than()
        new_p._is_proven = True
        return new_p

    def by_inspection(self) -> LessThan:
        """
        Logical tactic. Determine if the proposition is true by inspection.
        """
        try:
            if bool(self.left < self.right) is True:
                return LessThan(self.left, self.right, _is_proven=True)
            else:
                raise ValueError(
                    f"Cannot prove that {self.left} < {self.right} by inspection"
                )
        except TypeError:  # sympy raises TypeError if it can't determine the ordering
            raise ValueError(
                f"Cannot prove that {self.left} < {self.right} by inspection"
            )

    def __mul__(self, other: Term) -> LessThan:
        return super()._mul(self, other)

    def __rmul__(self, other: Term) -> LessThan:
        return super()._mul(self, other)
