from __future__ import annotations

from typing import TYPE_CHECKING, Callable, TypeVar

from pylogic.infix.infix import Infix
from pylogic.proposition.proposition import Proposition
from pylogic.symbol import Symbol

if TYPE_CHECKING:
    from fractions import Fraction


    from pylogic.expressions.expr import Expr
    from pylogic.proposition.relation.equals import Equals

    Numeric = Fraction | int | float
    PBasic = Symbol | Numeric
    UnevaluatedExpr = Symbol | Expr
    Term = UnevaluatedExpr | Numeric

P = TypeVar("P", bound=Proposition)


@Infix[Symbol, Callable[[Symbol], Proposition], Proposition]
def is_(a: Symbol, p: Callable[[Symbol], P]) -> P:
    return p(a)


is_a = is_


@Infix
def equals(a: Term, b: Term) -> Equals:
    from pylogic.proposition.relation.equals import Equals

    return Equals(a, b)
