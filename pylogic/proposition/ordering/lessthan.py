from __future__ import annotations
from fractions import Fraction
from typing import TYPE_CHECKING, overload
from pylogic.proposition.proposition import get_assumptions
from pylogic.proposition.relation.binaryrelation import BinaryRelation
from pylogic.proposition.ordering.ordering import _Ordering
from sympy import S as sympy_S

if TYPE_CHECKING:
    from pylogic.proposition.ordering.greaterthan import GreaterThan
    from pylogic.structures.sets import Set
    from pylogic.symbol import Symbol
    from pylogic.expressions.expr import Expr
    from sympy import Basic

    Numeric = Fraction | int | float
    PBasic = Symbol | Numeric
    UnevaluatedExpr = Symbol | Expr
    Term = UnevaluatedExpr | Numeric | Basic


class LessThan(BinaryRelation, _Ordering):
    is_transitive = True
    name = "LessThan"
    infix_symbol = "<"
    infix_symbol_latex = "<"

    @overload
    def __init__(
        self,
        left: Basic | Numeric,
        right: Basic | Numeric,
        is_assumption: bool = False,
        description: str = "",
        **kwargs,
    ) -> None: ...

    @overload
    def __init__(
        self,
        left: UnevaluatedExpr | Numeric,
        right: UnevaluatedExpr | Numeric,
        is_assumption: bool = False,
        description: str = "",
        **kwargs,
    ) -> None: ...

    @overload
    def __init__(
        self,
        left: Term,
        right: Term,
        is_assumption: bool = False,
        description: str = "",
        **kwargs,
    ) -> None: ...

    def __init__(
        self,
        left: Term,
        right: Term,
        is_assumption: bool = False,
        description: str = "",
        **kwargs,
    ) -> None:
        name = "LessThan"
        _is_proven = kwargs.get("_is_proven", False)
        diff = right - left
        if isinstance(diff, int) or isinstance(diff, float):
            diff_is_positive = diff > 0
        else:
            diff_is_positive = True
        if diff_is_positive == False and (is_assumption or _is_proven):
            raise ValueError(f"Some assumptions in {left}, {right} are contradictory")
        super().__init__(
            left, right, is_assumption=is_assumption, description=description, **kwargs
        )
        self.left: Term = left
        self.right: Term = right

    def to_positive_inequality(self):
        """If self is of the form a < b, returns an inequality of the form b - a > 0"""
        from pylogic.inference import Inference

        return GreaterThan(
            self.right - self.left,
            sympy_S.Zero,
            _is_proven=self.is_proven,
            _assumptions=get_assumptions(self),
            _inference=Inference(self, rule="to_positive_inequality"),
        )  # type: ignore

    def to_negative_inequality(self):
        """If self is of the form a < b, returns an inequality of the form a - b < 0"""
        from pylogic.inference import Inference

        return LessThan(
            self.left - self.right,
            sympy_S.Zero,
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
        from pylogic.inference import Inference

        try:
            if bool(self.left < self.right) is True:
                return LessThan(
                    self.left,
                    self.right,
                    _is_proven=True,
                    _assumptions=set(),
                    _inference=Inference(self, rule="by_inspection"),
                )  # type: ignore
            else:
                raise ValueError(
                    f"Cannot prove that {self.left} < {self.right} by inspection"
                )
        except TypeError:  # sympy raises TypeError if it can't determine the ordering
            raise ValueError(
                f"Cannot prove that {self.left} < {self.right} by inspection"
            )

    def __mul__(self, other: int | float) -> LessThan:
        return super()._mul(self, other)

    def __rmul__(self, other: int | float) -> LessThan:
        return super()._mul(self, other)
