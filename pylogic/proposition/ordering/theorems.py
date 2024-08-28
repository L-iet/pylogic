from __future__ import annotations

from typing import TYPE_CHECKING, overload

import sympy as sp

from pylogic.expressions.abs import Abs
from pylogic.expressions.expr import Expr
from pylogic.inference import Inference
from pylogic.proposition.implies import Implies
from pylogic.proposition.not_ import Not
from pylogic.proposition.or_ import Or
from pylogic.proposition.ordering.greaterthan import GreaterThan
from pylogic.proposition.ordering.lessthan import LessThan
from pylogic.proposition.quantified.forall import Forall
from pylogic.proposition.relation.equals import Equals
from pylogic.symbol import Symbol
from pylogic.variable import Variable, unbind

if TYPE_CHECKING:
    from fractions import Fraction

    Numeric = Fraction | int | float
    PBasic = Symbol | Numeric
    UnevaluatedExpr = Symbol | Expr
    Term = UnevaluatedExpr | Numeric


x = Variable("x", real=True)
y = Variable("y", real=True)

# forall x,y: x > y V x < y V x = y
order_axiom = Forall(
    x,
    Forall(
        y,
        Or(GreaterThan(x, y), LessThan(x, y), Equals(x, y)),
    ),
    is_assumption=True,
)
unbind(x, y)

# equals => not less than
order_axiom_b = Forall(
    x,
    Forall(y, Implies(Equals(x, y), Not(LessThan(x, y)))),
    is_assumption=True,
)
unbind(x, y)


@overload
def order_axiom_bf(
    x: UnevaluatedExpr | Numeric, y: UnevaluatedExpr | Numeric
) -> Implies[Equals, Not[LessThan]]: ...


@overload
def order_axiom_bf(
    x: sp.Basic | Numeric, y: sp.Basic | Numeric
) -> Implies[Equals, Not[LessThan]]: ...


def order_axiom_bf(x, y) -> Implies[Equals, Not[LessThan]]:
    return Implies(
        Equals(x, y),
        Not(LessThan(x, y)),
        _is_proven=True,
        _assumptions=set(),
        _inference=Inference(None, rule="order_axiom_bf"),
    )


# equals => not greater than
order_axiom_c = Forall(
    x,
    Forall(y, Implies(Equals(x, y), Not(GreaterThan(x, y)))),
    is_assumption=True,
)
unbind(x, y)

# less than => not equals
order_axiom_d = Forall(
    x,
    Forall(y, Implies(LessThan(x, y), Not(Equals(x, y)))),
    is_assumption=True,
)
unbind(x, y)

# less than => not greater than
order_axiom_e = Forall(
    x,
    Forall(y, Implies(LessThan(x, y), Not(GreaterThan(x, y)))),
    is_assumption=True,
)
unbind(x, y)

# greater than => not equals
order_axiom_f = Forall(
    x,
    Forall(y, Implies(GreaterThan(x, y), Not(Equals(x, y)))),
    is_assumption=True,
)
unbind(x, y)

# greater than => not less than
order_axiom_g = Forall(
    x,
    Forall(y, Implies(GreaterThan(x, y), Not(LessThan(x, y)))),
    is_assumption=True,
)
unbind(x, y)

absolute_value_nonnegative = Forall(
    x, Or(GreaterThan(Abs(x), 0), Equals(Abs(x), 0)), is_assumption=True
)


def absolute_value_nonnegative_f(x: Term) -> Or[GreaterThan, Equals]:
    """
    Logical tactic. If x is a real number, returns a proven proposition of the form Abs(x) > 0 V Abs(x) = 0.
    """
    abs_x = Abs(x)
    return Or(
        GreaterThan(abs_x, 0),
        Equals(abs_x, 0),
        _is_proven=True,
        _assumptions=set(),
        _inference=Inference(None, rule="absolute_value_nonnegative_f"),
    )
