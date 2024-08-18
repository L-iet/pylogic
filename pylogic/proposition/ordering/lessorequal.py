from __future__ import annotations
from typing import TYPE_CHECKING, overload
from fractions import Fraction

from pylogic.proposition.proposition import get_assumptions
from pylogic.proposition.ordering.lessthan import LessThan
from pylogic.proposition.relation.equals import Equals
from pylogic.proposition.relation.binaryrelation import BinaryRelation
from pylogic.proposition.ordering.ordering import _Ordering
from pylogic.inference import Inference


if TYPE_CHECKING:
    from pylogic.proposition.or_ import Or
    from pylogic.structures.set_ import Set
    from pylogic.symbol import Symbol
    from pylogic.expressions.expr import Expr
    from sympy import Basic

    Numeric = Fraction | int | float
    PBasic = Symbol | Numeric
    UnevaluatedExpr = Symbol | Expr
    Term = UnevaluatedExpr | Numeric | Basic


class LessOrEqual(BinaryRelation, _Ordering):
    is_transitive = True
    is_reflexive = True
    name = "LessThan"
    infix_symbol = "<="
    infix_symbol_latex = r"\leq"

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
        _is_proven = kwargs.get("_is_proven", False)
        name = "LessOrEqual"
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
