from __future__ import annotations
from typing import TYPE_CHECKING
from pylogic.proposition.quantified.exists import Exists
from pylogic.proposition.relation.equals import Equals
from pylogic.variable import Variable
from pylogic.proposition.and_ import And
from pylogic.expressions.expr import Expr, Mul, Pow

x = Variable("x")
y = Variable("y")

if TYPE_CHECKING:
    from pylogic.proposition.relation.contains import IsContainedIn
from pylogic.structures.set_ import Integers

if TYPE_CHECKING:
    from pylogic.symbol import Symbol
    from pylogic.structures.set_ import Set

    Term = Symbol | Set | Expr | int | float


def divisible(x: Symbol | int, y: Symbol | int, is_assumption=False) -> IsContainedIn:
    return Integers.contains(Mul(x, Pow(y, -1)), is_assumption=is_assumption)


# if x is divisible by y, then x has factors w and y for some integers a
_x_is_divisible_by_y = divisible(x, y, is_assumption=True)
_x_over_y_times_y_eq_x = Equals(Mul(x / y, y), x).by_simplification()
factors = (
    And(_x_is_divisible_by_y, _x_over_y_times_y_eq_x)
    .all_proven()
    .thus_there_exists("w", x / y)
    .followed_from(_x_is_divisible_by_y)
)
