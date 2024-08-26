from __future__ import annotations

from fractions import Fraction
from typing import Callable, Iterable, TypeAlias, TypeVar

from sympy import Basic
from sympy import Set as SympySet

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
Term = Unevaluated | Numeric | Basic

T = TypeVar("T", bound=Term)
BinOpFunc: TypeAlias = Callable[[T, T], BinaryExpression[T]]


class RightRingoid(_RingoidCommon):
    """
    A left-ringoid is a set closed under two binary operations + and *,
    where * left-distributes over +.
    """

    is_closed_under_plus: ForallInSet[ForallInSet[IsContainedIn]]
    is_closed_under_times: ForallInSet[ForallInSet[IsContainedIn]]
    times_right_dist_over_plus: ForallInSet[ForallInSet[ForallInSet[Equals]]]

    @classmethod
    def property_times_right_dist_over_plus(
        cls,
        set_: Set,
        plus_operation: SpecialInfix[
            Term, Term, BinaryExpression[Term], BinaryExpression[Term]
        ],
        times_operation: SpecialInfix[
            Term, Term, BinaryExpression[Term], BinaryExpression[Term]
        ],
    ) -> ForallInSet[ForallInSet[ForallInSet[Equals]]]:
        x = Variable("x")
        y = Variable("y")
        z = Variable("z")
        y_times_x = y | times_operation | x
        z_times_x = z | times_operation | x
        y_plus_z = y | plus_operation | z
        y_plus_z__times_x = y_plus_z | times_operation | x
        return ForallInSet(
            x,
            set_,
            ForallInSet(
                y,
                set_,
                ForallInSet(
                    z,
                    set_,
                    Equals(y_plus_z__times_x, (y_times_x | plus_operation | z_times_x)),
                ),
            ),
            description=f"{y_times_x.symbol} right-distributes over {y_plus_z.symbol} in {set_.name}",
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

        self.times_right_dist_over_plus = (
            RightRingoid.property_times_right_dist_over_plus(
                self, self.plus, self.times
            )
        )
        self.times_right_dist_over_plus.is_axiom = True
