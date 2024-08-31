from __future__ import annotations

from fractions import Fraction
from typing import TYPE_CHECKING, Any, TypeVar

from pylogic.proposition.ordering.ordering import _Ordering
from pylogic.proposition.relation.binaryrelation import BinaryRelation

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


class PartialOrder(BinaryRelation[T, U], _Ordering):
    is_transitive = True
    is_reflexive = True
    is_antisymmetric = True
    name = "PartialOrder"
    infix_symbol = "<="
    infix_symbol_latex = r"\leq"


class StrictPartialOrder(BinaryRelation[T, U], _Ordering):
    is_transitive = True
    is_irreflexive = True
    is_asymmetric = True
    name = "StrictPartialOrder"
    infix_symbol = "<"
    infix_symbol_latex = "<"
