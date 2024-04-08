from __future__ import annotations
from typing import TYPE_CHECKING
import sympy as sp
from pylogic.proposition.quantified.exists import Exists
from pylogic.proposition.relation.equals import Equals
from pylogic.variable import Variable
from pylogic.proposition.and_ import And

x = Variable("x")
y = Variable("y")

if TYPE_CHECKING:
    from pylogic.proposition.relation.contains import IsContainedIn
from pylogic.set.sets import Integers

if TYPE_CHECKING:
    from sympy import Basic

    SympyExpression = Basic | int | float


def divisible(
    x: SympyExpression, y: SympyExpression, is_assumption=False
) -> IsContainedIn:
    return Integers.contains(sp.Mul(x, sp.Pow(y, -1)), is_assumption=is_assumption)


# if x is divisible by y, then x has factors w and y for some integers a
_x_is_divisible_by_y = divisible(x, y, is_assumption=True)
_x_over_y_times_y_eq_x = Equals(sp.Mul(x / y, y, evaluate=False), x).by_simplification()
factors = (
    And(_x_is_divisible_by_y, _x_over_y_times_y_eq_x)
    .all_proven()
    .thus_there_exists("w", x / y)
    .followed_from(_x_is_divisible_by_y)
)
