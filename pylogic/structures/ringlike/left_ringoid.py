from __future__ import annotations

from fractions import Fraction
from typing import Callable, Iterable, TypeAlias, TypeVar


from pylogic.expressions.expr import BinaryExpression, Expr
from pylogic.infix.infix import SpecialInfix
from pylogic.proposition.quantified.forall import ForallInSet
from pylogic.proposition.relation.contains import IsContainedIn
from pylogic.proposition.relation.equals import Equals
from pylogic.structures.ringlike._ringoidcommon import _RingoidCommon
from pylogic.structures.set_ import Set
from pylogic.symbol import Symbol
from pylogic.variable import Variable

Numeric = Fraction | int | float
PBasic = Symbol | Numeric
Unevaluated = Symbol | Set | Expr
Term = Unevaluated | Numeric

T = TypeVar("T", bound=Term)
E = TypeVar("E", bound=Expr)
BinOpFunc: TypeAlias = Callable[[T, T], BinaryExpression[T]]


class LeftRingoid(_RingoidCommon):
    """
    A left-ringoid is a set closed under two binary operations + and *,
    where * left-distributes over +.
    """

    is_closed_under_plus: ForallInSet[ForallInSet[IsContainedIn]]
    is_closed_under_times: ForallInSet[ForallInSet[IsContainedIn]]
    times_left_dist_over_plus: ForallInSet[ForallInSet[ForallInSet[Equals]]]

    @classmethod
    def property_times_left_dist_over_plus(
        cls,
        set_: Set,
        plus_operation: SpecialInfix[Term, Term, Expr, Expr],
        times_operation: SpecialInfix[Term, Term, Expr, Expr],
    ) -> ForallInSet[ForallInSet[ForallInSet[Equals]]]:
        x = Variable("x")
        y = Variable("y")
        z = Variable("z")
        x_times_y = x | times_operation | y
        x_times_z = x | times_operation | z
        y_plus_z = y | plus_operation | z
        x_times__y_plus_z = x | times_operation | y_plus_z
        return ForallInSet(
            x,
            set_,
            ForallInSet(
                y,
                set_,
                ForallInSet(
                    z,
                    set_,
                    Equals(x_times__y_plus_z, (x_times_y | plus_operation | x_times_z)),
                ),
            ),
            description=f"{times_operation.symbol} left-distributes over {plus_operation.symbol} in {set_.name}",
        )

    def __init__(
        self,
        name: str,
        elements: Iterable[T] | None = None,
        containment_function: Callable[[T], bool] | None = None,
        plus_operation: Callable[[T, T], E] | None = None,
        plus_operation_symbol: str | None = None,
        times_operation: Callable[[T, T], E] | None = None,
        times_operation_symbol: str | None = None,
    ):
        # When initializing a ringoid, super() here points to
        # RightRingoid due to MRO
        super().__init__(
            name=name,
            elements=elements,
            containment_function=containment_function,
            plus_operation=plus_operation,
            plus_operation_symbol=plus_operation_symbol,
            times_operation=times_operation,
            times_operation_symbol=times_operation_symbol,
        )

        self.times_left_dist_over_plus = LeftRingoid.property_times_left_dist_over_plus(
            self, self.plus, self.times
        )
        self.times_left_dist_over_plus.is_axiom = True
