from __future__ import annotations

from fractions import Fraction
from typing import TYPE_CHECKING, Any, TypeVar

from pylogic.inference import Inference
from pylogic.proposition.ordering.lessthan import LessThan
from pylogic.proposition.ordering.ordering import _Ordering
from pylogic.proposition.proposition import get_assumptions
from pylogic.proposition.relation.binaryrelation import BinaryRelation
from pylogic.proposition.relation.equals import Equals

if TYPE_CHECKING:
    pass

    from pylogic.expressions.expr import Expr
    from pylogic.proposition.or_ import Or
    from pylogic.symbol import Symbol

    Numeric = Fraction | int | float
    PBasic = Symbol | Numeric
    UnevaluatedExpr = Symbol | Expr
    Term = UnevaluatedExpr | Numeric
else:
    Term = Any
T = TypeVar("T", bound=Term)
U = TypeVar("U", bound=Term)


class LessOrEqual(BinaryRelation, _Ordering[T, U]):
    is_transitive = True
    is_reflexive = True
    name = "LessThan"
    infix_symbol = "<="
    infix_symbol_latex = r"\leq"

    def __init__(
        self,
        left: T,
        right: U,
        is_assumption: bool = False,
        description: str = "",
        **kwargs,
    ) -> None:
        _is_proven = kwargs.get("_is_proven", False)
        diff = right - left
        if isinstance(diff, int) or isinstance(diff, float):
            diff_nonnegative = diff >= 0
        else:
            diff_nonnegative = True
        if diff_nonnegative == False and (is_assumption or _is_proven):
            raise ValueError(f"Some assumptions in {left}, {right} are contradictory")
        super().__init__(
            left, right, is_assumption=is_assumption, description=description, **kwargs
        )

    def to_disjunction(self) -> Or[LessThan, Equals]:
        """If self is of the form `a <= b`, returns a proposition of the form `a < b or a = b`"""
        return LessThan(self.left, self.right).or_(
            Equals(self.left, self.right),
            is_assumption=self.is_assumption,
            description=self.description,
            _is_proven=self._is_proven,
            _assumptions=get_assumptions(self),
            _inference=Inference(self, rule="to_disjunction"),
        )
