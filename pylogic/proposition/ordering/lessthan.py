from __future__ import annotations

from fractions import Fraction
from typing import TYPE_CHECKING, Any, TypeVar

from pylogic import Term
from pylogic.constant import Constant
from pylogic.proposition.ordering.ordering import _Ordering
from pylogic.proposition.ordering.total import StrictTotalOrder
from pylogic.proposition.proposition import get_assumptions
from pylogic.proposition.relation.binaryrelation import BinaryRelation

if TYPE_CHECKING:
    from pylogic.proposition.ordering.greaterthan import GreaterThan

T = TypeVar("T", bound=Term)
U = TypeVar("U", bound=Term)


class LessThan(StrictTotalOrder[T, U], _Ordering):
    name = "LessThan"
    infix_symbol = "<"
    infix_symbol_latex = "<"

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
            name="LessThan",
            is_assumption=is_assumption,
            description=description,
            **kwargs,
        )

    def to_positive_inequality(self):
        """If self is of the form a < b, returns an inequality of the form b - a > 0"""
        from pylogic.inference import Inference

        return GreaterThan(
            self.right - self.left,
            Constant(0),
            _is_proven=self.is_proven,
            _assumptions=get_assumptions(self),
            _inference=Inference(self, rule="to_positive_inequality"),
        )  # type: ignore

    def to_negative_inequality(self):
        """If self is of the form a < b, returns an inequality of the form a - b < 0"""
        from pylogic.inference import Inference

        return LessThan(
            self.left - self.right,
            Constant(0),
            _is_proven=self.is_proven,
            _assumptions=get_assumptions(self),
            _inference=Inference(self, rule="to_negative_inequality"),
        )  # type: ignore

    def multiply_by_positive(
        self, x: Term, proof_x_is_positive: "GreaterThan | LessThan"
    ) -> "LessThan":
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
    ) -> "LessThan":
        from pylogic.inference import Inference

        new_p = super()._multiply_by(
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
        return new_p

    def p_multiply_by_positive(
        self, x: Term, proof_x_is_positive: "GreaterThan | LessThan"
    ) -> "LessThan":
        """Logical tactic.
        Same as multiply_by_positive, but returns a proven proposition"""

        assert self.is_proven, f"{self} is not proven"
        new_p = self.multiply_by_positive(x, proof_x_is_positive)
        return new_p

    def p_multiply_by_negative(
        self, x: Term, proof_x_is_negative: "GreaterThan | LessThan"
    ) -> "LessThan":
        """Logical tactic.
        Same as multiply_by_negative, but returns a proven proposition"""

        assert self.is_proven, f"{self} is not proven"
        new_p = self.multiply_by_negative(x, proof_x_is_negative)
        return new_p

    def mul_inverse(self):
        from pylogic.inference import Inference

        return LessThan(
            1 / self.right,
            1 / self.left,
            _is_proven=self.is_proven,
            _assumptions=get_assumptions(self),
            _inference=Inference(self, rule="mul_inverse"),
        )  # type: ignore

    def to_greater_than(self):
        """If self is of the form a < b, returns an inequality of the form b > a"""
        from pylogic.inference import Inference

        return GreaterThan(
            self.right,
            self.left,
            _is_proven=self.is_proven,
            _assumptions=get_assumptions(self),
            _inference=Inference(self, rule="to_greater_than"),
        )  # type: ignore

    def p_to_greater_than(self):
        """Logical tactic. Same as to_greater_than, but returns a proven proposition"""
        assert self.is_proven, f"{self} is not proven"
        new_p = self.to_greater_than()
        return new_p

    def by_inspection(self) -> LessThan:
        """
        Logical tactic. Determine if the proposition is true by inspection.
        """
        raise NotImplementedError

    def __mul__(self, other: int | float) -> LessThan:
        return super()._mul(self, other)

    def __rmul__(self, other: int | float) -> LessThan:
        return super()._mul(self, other)
