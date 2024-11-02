from __future__ import annotations

from typing import Callable, Iterable, TypeAlias, TypeVar

from pylogic import Term
from pylogic.expressions.expr import BinaryExpression, Expr
from pylogic.infix.infix import SpecialInfix
from pylogic.proposition.quantified.forall import ForallInSet
from pylogic.proposition.relation.contains import IsContainedIn
from pylogic.proposition.relation.equals import Equals
from pylogic.structures.ringlike._ringoidcommon import _RingoidCommon
from pylogic.structures.set_ import Set
from pylogic.variable import Variable

T = TypeVar("T", bound=Term)
E = TypeVar("E", bound=Expr)
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
        plus_operation: SpecialInfix[Term, Term, Expr, Expr],
        times_operation: SpecialInfix[Term, Term, Expr, Expr],
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
            description=f"{times_operation.symbol} right-distributes over {plus_operation.symbol} in {set_.name}",
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
        **kwargs,
    ):
        super().__init__(
            name=name,
            elements=elements,
            containment_function=containment_function,
            plus_operation=plus_operation,
            plus_operation_symbol=plus_operation_symbol,
            times_operation=times_operation,
            times_operation_symbol=times_operation_symbol,
            **kwargs,
        )

        self.times_right_dist_over_plus = (
            RightRingoid.property_times_right_dist_over_plus(
                self, self.plus, self.times
            )
        )
        self.times_right_dist_over_plus._set_is_axiom(True)
