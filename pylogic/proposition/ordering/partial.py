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
    """
    Parameters
    ----------
    name : str
        The name of the partial order.
    left : T
        The left term of the partial order.
    right : U
        The right term of the partial order.

    Also receives the same parameters as BinaryRelation.
    """

    is_transitive = True
    is_reflexive = True
    is_antisymmetric = True
    name = "PartialOrder"
    infix_symbol = "<="
    infix_symbol_latex = r"\leq"

    def __init__(
        self,
        left: T,
        right: U,
        name: str = "PartialOrder",
        is_assumption: bool = False,
        description: str = "",
        **kwargs,
    ) -> None:
        super().__init__(
            left,
            right,
            is_assumption=is_assumption,
            description=description,
            **kwargs,
        )
        self.name = name


class StrictPartialOrder(BinaryRelation[T, U], _Ordering):
    """
    Parameters
    ----------
    name : str
        The name of the strict partial order.
    left : T
        The left term of the strict partial order.
    right : U
        The right term of the strict partial order.

    Also receives the same parameters as BinaryRelation.
    """

    is_transitive = True
    is_irreflexive = True
    is_asymmetric = True
    name = "StrictPartialOrder"
    infix_symbol = "<"
    infix_symbol_latex = "<"

    def __init__(
        self,
        left: T,
        right: U,
        name: str = "StrictPartialOrder",
        is_assumption: bool = False,
        description: str = "",
        **kwargs,
    ) -> None:
        super().__init__(
            left,
            right,
            is_assumption=is_assumption,
            description=description,
            **kwargs,
        )
        self.name = name
