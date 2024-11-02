from __future__ import annotations

from typing import Callable, Iterable, TypeVar

from pylogic import Term
from pylogic.expressions.expr import Expr
from pylogic.infix.infix import SpecialInfix
from pylogic.proposition.quantified.forall import ForallInSet
from pylogic.proposition.relation.equals import Equals
from pylogic.structures.grouplike.magma import Magma
from pylogic.structures.set_ import Set
from pylogic.variable import Variable

T = TypeVar("T", bound=Term)
E = TypeVar("E", bound=Expr)


class Semigroup(Magma):
    op_is_associative: ForallInSet[ForallInSet[ForallInSet[Equals]]]

    @classmethod
    def property_op_is_associative(
        cls,
        set_: Set,
        operation: SpecialInfix[Term, Term, Expr, Expr],
    ) -> ForallInSet[ForallInSet[ForallInSet[Equals]]]:
        x = Variable("x")
        y = Variable("y")
        z = Variable("z")
        x_op_y = x | operation | y
        x_op_y_op_z = x_op_y | operation | z
        return ForallInSet(
            x,
            set_,
            ForallInSet(
                y,
                set_,
                ForallInSet(
                    z,
                    set_,
                    Equals(x_op_y_op_z, x | operation | (y | operation | z)),
                ),
            ),
            description=f"{operation.symbol} is associative in {set_.name}",
        )

    def __init__(
        self,
        name: str,
        elements: Iterable[T] | None = None,
        containment_function: Callable[[T], bool] | None = None,
        operation: Callable[[T, T], E] | None = None,
        operation_name: str | None = None,
        operation_symbol: str | None = None,
        **kwargs,
    ):
        Magma.__init__(
            self,
            name=name,
            elements=elements,
            containment_function=containment_function,
            operation=operation,
            operation_name=operation_name,
            operation_symbol=operation_symbol,
        )
        self._init_args = (name,)
        self._init_kwargs = {
            "elements": elements,
            "containment_function": containment_function,
            "operation": operation,
            "operation_name": operation_name,
            "operation_symbol": operation_symbol,
        }
        self._init_kwargs.update(kwargs)
        self.op_is_associative = Semigroup.property_op_is_associative(
            self, self.operation
        )
        self.op_is_associative._set_is_axiom(True)
