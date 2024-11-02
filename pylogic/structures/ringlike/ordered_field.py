from __future__ import annotations

from fractions import Fraction
from typing import TYPE_CHECKING, Any, Callable, Iterable, TypeAlias, TypeVar

from pylogic import Term, Unevaluated
from pylogic.expressions.expr import BinaryExpression, Expr
from pylogic.proposition.and_ import And
from pylogic.proposition.implies import Implies
from pylogic.proposition.ordering.total import StrictTotalOrder, TotalOrder
from pylogic.proposition.quantified.forall import ForallInSet
from pylogic.structures.ordered_set import OrderedSet
from pylogic.structures.ringlike.field import Field
from pylogic.structures.set_ import Set
from pylogic.variable import Variable

if TYPE_CHECKING:
    from pylogic.infix.infix import SpecialInfix

    T = TypeVar("T", bound=Term)
    E = TypeVar("E", bound=Expr)
    Z = TypeVar("Z", str, int, float, complex, Fraction)
    BinOpFunc: TypeAlias = Callable[[T, T], BinaryExpression[T]]
    TotalOrderOp: TypeAlias = Callable[..., TotalOrder]
    StrictTotalOrderOp: TypeAlias = Callable[..., StrictTotalOrder]
else:
    Term = Any
    T = Any
    E = Any
    Z = Any
    BinOpFunc = Any
    TotalOrderOp = Any
    StrictTotalOrderOp = Any


class OrderedField(Field[Z], OrderedSet):
    add_to_both_sides_of_inequality: ForallInSet[
        ForallInSet[ForallInSet[Implies[TotalOrder, TotalOrder]]]
    ]
    product_of_nonnegatives_is_nonnegative: ForallInSet[
        ForallInSet[Implies[And[TotalOrder, TotalOrder], TotalOrder]]
    ]

    @classmethod
    def property_add_to_both_sides_of_inequality(
        cls,
        set_: Set,
        total_order: TotalOrderOp,
        plus_operation: SpecialInfix[Term, Term, Expr, Expr],
    ) -> ForallInSet[ForallInSet[ForallInSet[Implies[TotalOrder, TotalOrder]]]]:
        a = Variable("a")
        b = Variable("b")
        c = Variable("c")
        a_le_b = total_order(a, b)
        a_plus_c_le_b_plus_c = total_order(plus_operation(a, c), plus_operation(b, c))
        return ForallInSet(
            a,
            set_,
            ForallInSet(
                b,
                set_,
                ForallInSet(
                    c,
                    set_,
                    Implies(
                        a_le_b,
                        a_plus_c_le_b_plus_c,
                    ),
                ),
            ),
            description=f"add to both sides of (total order) inequality in {set_}",
        )

    @classmethod
    def property_product_of_nonnegatives_is_nonnegative(
        cls,
        set_: Set,
        total_order: TotalOrderOp,
        times_operation: SpecialInfix[Term, Term, Expr, Expr],
    ) -> ForallInSet[ForallInSet[Implies[And[TotalOrder, TotalOrder], TotalOrder]]]:
        """
        Assuming the total order is a <= b, return
        0 <= a and 0 <= b implies 0 <= a*b
        """
        a = Variable("a")
        b = Variable("b")
        a_ge_0 = total_order(0, a)
        b_ge_0 = total_order(0, b)
        a_times_b_ge_0 = total_order(0, times_operation(a, b))
        return ForallInSet(
            a,
            set_,
            ForallInSet(
                b,
                set_,
                Implies(
                    And(a_ge_0, b_ge_0),
                    a_times_b_ge_0,
                ),
            ),
            description=f"product of nonnegatives is nonnegative in {set_}",
        )

    def __init__(
        self,
        name: str,
        elements: Iterable[T] | None = None,
        containment_function: Callable[[T], bool] | None = None,
        plus_operation: Callable[[T, T], E] | None = None,
        plus_operation_symbol: str | None = None,
        zero: Z | Unevaluated | None = None,
        times_operation: Callable[[T, T], E] | None = None,
        times_operation_symbol: str | None = None,
        one: Z | Unevaluated | None = None,
        total_order: TotalOrderOp | None = None,
        strict_total_order: StrictTotalOrderOp | None = None,
        **kwargs,
    ):
        # explicitly call __init__ of both superclasses due to mro
        Field.__init__(
            self,
            name=name,
            elements=elements,
            containment_function=containment_function,
            plus_operation=plus_operation,
            plus_operation_symbol=plus_operation_symbol,
            zero=zero,
            times_operation=times_operation,
            times_operation_symbol=times_operation_symbol,
            one=one,
            **kwargs,
        )
        OrderedSet.__init__(
            self,
            name=name,
            elements=elements,
            containment_function=containment_function,  # type: ignore
            total_order=total_order,
            strict_total_order=strict_total_order,
            **kwargs,
        )
        self._init_args = (name,)
        self._init_kwargs = {
            "elements": elements,
            "containment_function": containment_function,
            "plus_operation": plus_operation,
            "plus_operation_symbol": plus_operation_symbol,
            "zero": zero,
            "times_operation": times_operation,
            "times_operation_symbol": times_operation_symbol,
            "one": one,
            "total_order": total_order,
            "strict_total_order": strict_total_order,
        }
        self._init_kwargs.update(kwargs)

        self.add_to_both_sides_of_inequality = (
            OrderedField.property_add_to_both_sides_of_inequality(
                self, self.total_order, self.plus_operation
            )
        )
        self.add_to_both_sides_of_inequality._set_is_axiom(True)

        self.product_of_nonnegatives_is_nonnegative = (
            OrderedField.property_product_of_nonnegatives_is_nonnegative(
                self, self.total_order, self.times_operation
            )
        )
        self.product_of_nonnegatives_is_nonnegative._set_is_axiom(True)

        # TODO proving a <= 0 implies -a >= 0 (can use add -a to both sides)
        ...
