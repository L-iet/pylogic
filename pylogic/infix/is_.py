from __future__ import annotations
from typing import Callable, TYPE_CHECKING, TypeVar
from pylogic.infix.infix import Infix
from pylogic.symbol import Symbol
from pylogic.proposition.proposition import Proposition

if TYPE_CHECKING:
    from fractions import Fraction
    from pylogic.expressions.expr import Expr
    from sympy import Basic
    from pylogic.proposition.relation.equals import Equals

    Numeric = Fraction | int | float
    PBasic = Symbol | Numeric
    UnevaluatedExpr = Symbol | Expr
    Term = UnevaluatedExpr | Numeric | Basic

P = TypeVar("P", bound=Proposition)


@Infix[Symbol, Callable[[Symbol], Proposition], Proposition]
def is_(a: Symbol, p: Callable[[Symbol], P]) -> P:
    return p(a)


is_a = is_


@Infix
def equals(a: Term, b: Term) -> Equals:
    from pylogic.proposition.relation.equals import Equals

    return Equals(a, b)
