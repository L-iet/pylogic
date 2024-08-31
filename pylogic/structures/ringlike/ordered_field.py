from __future__ import annotations

from fractions import Fraction
from typing import TYPE_CHECKING, Callable, Iterable, TypeAlias, TypeVar

from pylogic.expressions.expr import BinaryExpression, Expr
from pylogic.infix.infix import SpecialInfix
from pylogic.proposition.quantified.forall import ForallInSet
from pylogic.proposition.relation.equals import Equals
from pylogic.structures.grouplike.group import AbelianGroup
from pylogic.structures.ringlike.division_ring import DivisionRIng
from pylogic.structures.ringlike.field import Field
from pylogic.structures.set_ import Set
from pylogic.symbol import Symbol
from pylogic.variable import Variable

if TYPE_CHECKING:
    from pylogic.proposition.and_ import And
    from pylogic.proposition.implies import Implies
    from pylogic.proposition.or_ import Or
    from pylogic.proposition.ordering.total import TotalOrder

    Numeric = Fraction | int | float
    PBasic = Symbol | Numeric
    Unevaluated = Symbol | Set | Expr
    Term = Unevaluated | Numeric

    T = TypeVar("T", bound=Term)
    E = TypeVar("E", bound=Expr)
    Z = TypeVar("Z", str, int, float, complex, Fraction)
    BinOpFunc: TypeAlias = Callable[[T, T], BinaryExpression[T]]
    TotalOrderOp: TypeAlias = Callable[..., TotalOrder]
else:
    Term = Any
    T = Any
    E = Any
    Z = Any
    BinOpFunc = Any
    TotalOrderOp = Any


class OrderedField(Field[Z]):
    order_is_reflexive: ForallInSet[TotalOrder]
    order_is_transitive: ForallInSet[
        ForallInSet[ForallInSet[Implies[And[TotalOrder, TotalOrder], TotalOrder]]]
    ]
    order_is_antisymmetric: ForallInSet[
        ForallInSet[Implies[And[TotalOrder, TotalOrder], Equals]]
    ]
    order_is_strongly_connected: ForallInSet[ForallInSet[Or[TotalOrder, TotalOrder]]]

    @classmethod
    def property_order_is_reflexive(
        cls, set_: Set, total_order: TotalOrderOp
    ) -> ForallInSet[TotalOrder]:
        a = Variable("a")
        return ForallInSet(
            a,
            set_,
            total_order(a, a),
            description=f"{total_order} is reflexive in {set_}",
        )

    @classmethod
    def property_order_is_transitive(
        cls, set_: Set, total_order: TotalOrderOp
    ) -> ForallInSet[
        ForallInSet[ForallInSet[Implies[And[TotalOrder, TotalOrder], TotalOrder]]]
    ]:
        a = Variable("a")
        b = Variable("b")
        c = Variable("c")
        a_le_b = total_order(a, b)
        b_le_c = total_order(b, c)
        a_le_c = total_order(a, c)
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
                        And(a_le_b, b_le_c),
                        a_le_c,
                    ),
                ),
            ),
            description=f"{total_order} is transitive in {set_}",
        )

    @classmethod
    def property_order_is_antisymmetric(
        cls, set_: Set, total_order: TotalOrderOp
    ) -> ForallInSet[ForallInSet[Implies[And[TotalOrder, TotalOrder], Equals]]]:
        a = Variable("a")
        b = Variable("b")
        a_le_b = total_order(a, b)
        b_le_a = total_order(b, a)
        return ForallInSet(
            a,
            set_,
            ForallInSet(
                b,
                set_,
                Implies(
                    And(a_le_b, b_le_a),
                    Equals(a, b),
                ),
            ),
            description=f"{total_order} is antisymmetric in {set_}",
        )

    @classmethod
    def property_order_is_strongly_connected(
        cls, set_: Set, total_order: TotalOrderOp
    ) -> ForallInSet[ForallInSet[Or[TotalOrder, TotalOrder]]]:
        a = Variable("a")
        b = Variable("b")
        a_le_b = total_order(a, b)
        b_le_a = total_order(b, a)
        return ForallInSet(
            a,
            set_,
            ForallInSet(
                b,
                set_,
                Or(
                    a_le_b,
                    b_le_a,
                ),
            ),
            description=f"{total_order} is strongly connected in {set_}",
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
    ):
        super().__init__(
            name=name,
            elements=elements,
            containment_function=containment_function,
            plus_operation=plus_operation,
            plus_operation_symbol=plus_operation_symbol,
            zero=zero,
            times_operation=times_operation,
            times_operation_symbol=times_operation_symbol,
            one=one,
        )
        self.total_order: Callable[..., TotalOrder] = total_order or (
            lambda x, y: TotalOrder(x, y)
        )
        self.order_is_reflexive = OrderedField.property_order_is_reflexive(
            self, self.total_order
        )
        self.order_is_reflexive.is_axiom = True
        self.order_is_transitive = OrderedField.property_order_is_transitive(
            self, self.total_order
        )
        self.order_is_transitive.is_axiom = True
        self.order_is_antisymmetric = OrderedField.property_order_is_antisymmetric(
            self, self.total_order
        )
        self.order_is_antisymmetric.is_axiom = True
        self.order_is_strongly_connected = (
            OrderedField.property_order_is_strongly_connected(self, self.total_order)
        )
        self.order_is_strongly_connected.is_axiom = True
