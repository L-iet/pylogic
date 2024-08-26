from __future__ import annotations
from typing import Callable, Iterable, TypeVar, TypeAlias
from fractions import Fraction
from pylogic.structures.set_ import Set
from pylogic.infix.infix import SpecialInfix
from pylogic.expressions.expr import BinaryExpression, Expr
from pylogic.symbol import Symbol
from pylogic.variable import Variable
from pylogic.proposition.quantified.forall import ForallInSet
from pylogic.proposition.relation.contains import IsContainedIn
from pylogic.proposition.relation.equals import Equals
from pylogic.proposition.and_ import And

from pylogic.structures.grouplike.magma import Magma
from pylogic.structures.ringlike.left_ringoid import LeftRingoid
from pylogic.structures.ringlike.right_ringoid import RightRingoid

from sympy import Basic
from sympy import Set as SympySet

Numeric = Fraction | int | float
PBasic = Symbol | Numeric
Unevaluated = Symbol | Set | Expr
Term = Unevaluated | Numeric | Basic

T = TypeVar("T", bound=Term)
BinOpFunc: TypeAlias = Callable[[T, T], BinaryExpression[T]]


class Ringoid(LeftRingoid, RightRingoid):
    """
    A ringoid is a set closed under two binary operations + and *,
    where * distributes over +.
    """

    is_closed_under_plus: ForallInSet[ForallInSet[IsContainedIn]]
    is_closed_under_times: ForallInSet[ForallInSet[IsContainedIn]]
    times_dist_over_plus: And[
        ForallInSet[ForallInSet[ForallInSet[Equals]]],
        ForallInSet[ForallInSet[ForallInSet[Equals]]],
    ]

    @classmethod
    def property_times_dist_over_plus(
        cls,
        set_: Set,
        plus_operation: SpecialInfix[
            Term, Term, BinaryExpression[Term], BinaryExpression[Term]
        ],
        times_operation: SpecialInfix[
            Term, Term, BinaryExpression[Term], BinaryExpression[Term]
        ],
    ) -> And[
        ForallInSet[ForallInSet[ForallInSet[Equals]]],
        ForallInSet[ForallInSet[ForallInSet[Equals]]],
    ]:
        x = Variable("x")
        y = Variable("y")
        x_plus_y = x | plus_operation | y
        x_times_y = x | times_operation | y

        return And(
            LeftRingoid.property_times_left_dist_over_plus(
                set_, plus_operation, times_operation
            ),
            RightRingoid.property_times_right_dist_over_plus(
                set_, plus_operation, times_operation
            ),
            description=f"{x_times_y.symbol} distributes over {x_plus_y.symbol} in {set_.name}",
        )

    def __init__(
        self,
        name: str | None = None,
        sympy_set: SympySet | None = None,
        elements: Iterable[T] | None = None,
        containment_function: Callable[[T], bool] | None = None,
        plus_operation: Callable[[T, T], T] | None = None,
        plus_operation_symbol: str | None = None,
        times_operation: Callable[[T, T], T] | None = None,
        times_operation_symbol: str | None = None,
    ):
        # LeftRingoid.__init__
        super().__init__(
            name=name,
            sympy_set=sympy_set,
            elements=elements,
            containment_function=containment_function,
            plus_operation=plus_operation,
            plus_operation_symbol=plus_operation_symbol,
            times_operation=times_operation,
            times_operation_symbol=times_operation_symbol,
        )

        self.times_dist_over_plus = And(
            self.times_left_dist_over_plus,
            self.times_right_dist_over_plus,
        ).all_proven()


x = Variable("x")
y = Variable("y")
z = Variable("z")
R = Ringoid("R", elements={x, y, z}, times_operation=lambda x, y: x * y)
w = x | R.times | z
print(R.times_right_dist_over_plus.is_proven)