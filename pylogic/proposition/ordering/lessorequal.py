from __future__ import annotations

from fractions import Fraction
from typing import TYPE_CHECKING, Any, TypeVar

from pylogic.inference import Inference
from pylogic.proposition.ordering.lessthan import LessThan
from pylogic.proposition.ordering.ordering import _Ordering
from pylogic.proposition.ordering.total import TotalOrder
from pylogic.proposition.proposition import get_assumptions
from pylogic.proposition.relation.equals import Equals

if TYPE_CHECKING:
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


class LessOrEqual(TotalOrder[T, U], _Ordering):
    name = "LessThan"
    infix_symbol = "<="
    infix_symbol_latex = r"\leq"

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
