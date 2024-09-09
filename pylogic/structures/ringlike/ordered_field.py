from __future__ import annotations

from fractions import Fraction
from typing import TYPE_CHECKING, Any, Callable, Iterable, TypeAlias, TypeVar, cast

from pylogic.expressions.expr import BinaryExpression, Expr
from pylogic.proposition.and_ import And
from pylogic.proposition.iff import Iff
from pylogic.proposition.implies import Implies
from pylogic.proposition.not_ import Not, neg
from pylogic.proposition.or_ import Or
from pylogic.proposition.ordering.total import StrictTotalOrder, TotalOrder
from pylogic.proposition.quantified.forall import ForallInSet
from pylogic.proposition.relation.equals import Equals
from pylogic.structures.ringlike.field import Field
from pylogic.structures.set_ import Set
from pylogic.symbol import Symbol
from pylogic.variable import Variable

if TYPE_CHECKING:
    Numeric = Fraction | int | float
    PBasic = Symbol | Numeric
    Unevaluated = Symbol | Set | Expr
    Term = Unevaluated | Numeric

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


class OrderedField(Field[Z]):
    strict_order_definition: ForallInSet[
        ForallInSet[Iff[StrictTotalOrder, And[TotalOrder, Not[Equals]]]]
    ]
    order_definition: ForallInSet[
        ForallInSet[Iff[TotalOrder, Or[StrictTotalOrder, Equals]]]
    ]
    order_is_reflexive: ForallInSet[TotalOrder]
    order_is_transitive: ForallInSet[
        ForallInSet[ForallInSet[Implies[And[TotalOrder, TotalOrder], TotalOrder]]]
    ]
    order_is_antisymmetric: ForallInSet[
        ForallInSet[Implies[And[TotalOrder, TotalOrder], Equals]]
    ]
    order_is_strongly_connected: ForallInSet[ForallInSet[Or[TotalOrder, TotalOrder]]]
    strict_order_is_irreflexive: ForallInSet[Not[StrictTotalOrder]]
    strict_order_is_asymmetric: ForallInSet[
        ForallInSet[Implies[StrictTotalOrder, Not[StrictTotalOrder]]]
    ]
    strict_order_is_transitive: ForallInSet[
        ForallInSet[
            ForallInSet[
                Implies[And[StrictTotalOrder, StrictTotalOrder], StrictTotalOrder]
            ]
        ]
    ]
    strict_order_is_connected: ForallInSet[
        ForallInSet[Implies[Not[Equals], Or[StrictTotalOrder, StrictTotalOrder]]]
    ]
    strict_total_order: StrictTotalOrderOp
    total_order: TotalOrderOp

    @classmethod
    def property_order_definition(
        cls,
        set_: Set,
        total_order: TotalOrderOp,
        strict_total_order: StrictTotalOrderOp,
    ) -> ForallInSet[ForallInSet[Iff[TotalOrder, Or[StrictTotalOrder, Equals]]]]:
        x, y = Variable("x"), Variable("y")
        return ForallInSet(
            x,
            set_,
            ForallInSet(
                y,
                set_,
                Iff(
                    total_order(x, y),
                    Or(strict_total_order(x, y), Equals(x, y)),
                ),
            ),
            description=f"total order definition",
        )

    @classmethod
    def property_strict_order_definition(
        cls,
        set_: Set,
        total_order: TotalOrderOp,
        strict_total_order: StrictTotalOrderOp,
    ) -> ForallInSet[ForallInSet[Iff[StrictTotalOrder, And[TotalOrder, Not[Equals]]]]]:
        x, y = Variable("x"), Variable("y")
        return ForallInSet(
            x,
            set_,
            ForallInSet(
                y,
                set_,
                Iff(
                    strict_total_order(x, y),
                    And(total_order(x, y), neg(Equals(x, y))),
                ),
            ),
            description=f"strict total order definition",
        )

    @classmethod
    def property_order_is_reflexive(
        cls, set_: Set, total_order: TotalOrderOp
    ) -> ForallInSet[TotalOrder]:
        a = Variable("a")
        return ForallInSet(
            a,
            set_,
            total_order(a, a),
            description=f"total order is reflexive in {set_}",
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
                    And(a_le_b, b_le_c).implies(a_le_c),
                ),
            ),
            description=f"total order is transitive in {set_}",
        )  # type: ignore

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
            description=f"total order is antisymmetric in {set_}",
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
            description=f"total order is strongly connected in {set_}",
        )

    @classmethod
    def property_strict_order_is_irreflexive(
        cls, set_: Set, strict_total_order: StrictTotalOrderOp
    ) -> ForallInSet[Not[StrictTotalOrder]]:
        a = Variable("a")
        return ForallInSet(
            a,
            set_,
            Not(strict_total_order(a, a)),
            description=f"strict total order is irreflexive in {set_}",
        )

    @classmethod
    def property_strict_order_is_asymmetric(
        cls, set_: Set, strict_total_order: StrictTotalOrderOp
    ) -> ForallInSet[ForallInSet[Implies[StrictTotalOrder, Not[StrictTotalOrder]]]]:
        a = Variable("a")
        b = Variable("b")
        a_lt_b = strict_total_order(a, b)
        b_lt_a = strict_total_order(b, a)
        return ForallInSet(
            a,
            set_,
            ForallInSet(
                b,
                set_,
                Implies(
                    a_lt_b,
                    Not(b_lt_a),
                ),
            ),
            description=f"strict total order is asymmetric in {set_}",
        )

    @classmethod
    def property_strict_order_is_transitive(
        cls, set_: Set, strict_total_order: StrictTotalOrderOp
    ) -> ForallInSet[
        ForallInSet[
            ForallInSet[
                Implies[And[StrictTotalOrder, StrictTotalOrder], StrictTotalOrder]
            ]
        ]
    ]:
        a = Variable("a")
        b = Variable("b")
        c = Variable("c")
        a_lt_b = strict_total_order(a, b)
        b_lt_c = strict_total_order(b, c)
        a_lt_c = strict_total_order(a, c)
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
                        And(a_lt_b, b_lt_c),
                        a_lt_c,
                    ),
                ),
            ),
            description=f"strict total order is transitive in {set_}",
        )

    @classmethod
    def property_strict_order_is_connected(
        cls, set_: Set, strict_total_order: StrictTotalOrderOp
    ) -> ForallInSet[
        ForallInSet[Implies[Not[Equals], Or[StrictTotalOrder, StrictTotalOrder]]]
    ]:
        a = Variable("a")
        b = Variable("b")
        a_ne_b = neg(Equals(a, b))
        a_lt_b = strict_total_order(a, b)
        b_lt_a = strict_total_order(b, a)
        return ForallInSet(
            a,
            set_,
            ForallInSet(
                b,
                set_,
                Implies(
                    a_ne_b,
                    Or(
                        a_lt_b,
                        b_lt_a,
                    ),
                ),
            ),
            description=f"strict total order is connected in {set_}",
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
        self._build_total_and_strict_orders(total_order, strict_total_order)
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

        self.order_definition = OrderedField.property_order_definition(
            self, self.total_order, self.strict_total_order
        )
        self.order_definition.is_axiom = True
        self.strict_order_definition = OrderedField.property_strict_order_definition(
            self, self.total_order, self.strict_total_order
        )
        self.strict_order_definition.is_axiom = True

        a, b, c = Variable("a"), Variable("b"), Variable("c")
        a_in_self = a.is_in(self, is_assumption=True)
        b_in_self = b.is_in(self, is_assumption=True)
        c_in_self = c.is_in(self, is_assumption=True)
        # Strict order properties are theorems if we have defined total order properties
        # 1. Strict order is irreflexive
        step_1 = self.strict_order_definition.in_particular(a, a_in_self).in_particular(
            a, a_in_self
        )
        step_2 = step_1.contrapositive()
        a_nlt_a_or_a_eq_a = (
            neg(self.total_order(a, a))
            .or_(Equals(a, a))
            .one_proven(Equals.reflexive(a))
        )
        a_nlt_a_or_a_eq_a = a_nlt_a_or_a_eq_a.de_morgan()
        self.strict_order_is_irreflexive = a_nlt_a_or_a_eq_a.modus_ponens(
            step_2.forward_implication()  # type: ignore
        ).thus_forall_in_set(a, self)

        # 2. Strict order is asymmetric
        a_lt_b = self.strict_total_order(a, b, is_assumption=True)
        step_1 = (
            self.strict_order_definition.in_particular(a, a_in_self)
            .in_particular(b, b_in_self)
            .forward_implication()
        )
        a_leq_b, a_neq_b = a_lt_b.modus_ponens(step_1).extract()
        step_2 = (
            self.order_is_antisymmetric.in_particular(a, a_in_self)
            .in_particular(b, b_in_self)
            .contrapositive()
        )
        step_3: Or = a_neq_b.modus_ponens(step_2).de_morgan()  # type: ignore
        b_nleq_a = step_3.unit_resolve(a_leq_b)  # type: ignore
        step_4 = (
            self.order_definition.in_particular(b, b_in_self)
            .in_particular(a, a_in_self)
            .inverse()
            .forward_implication()
        )
        b_nlt_a, _ = b_nleq_a.modus_ponens(step_4).de_morgan().extract()  # type: ignore
        b_nlt_a = cast(Not[StrictTotalOrder], b_nlt_a)
        self.strict_order_is_asymmetric = (
            b_nlt_a.followed_from(a_lt_b)
            .thus_forall_in_set(b, self)
            .thus_forall_in_set(a, self)
        )

    def _build_total_and_strict_orders(
        self,
        total_order: TotalOrderOp | None,
        strict_total_order: StrictTotalOrderOp | None,
    ) -> None:
        from pylogic.proposition.ordering.greaterorequal import GreaterOrEqual
        from pylogic.proposition.ordering.greaterthan import GreaterThan
        from pylogic.proposition.ordering.lessorequal import LessOrEqual
        from pylogic.proposition.ordering.lessthan import LessThan

        class _CustomStrictTotalOrder(StrictTotalOrder):
            def __init__(inst, *args, **kwargs):
                super().__init__(*args, **kwargs)
                inst.name = f"{self.name}_<"

        class _CustomTotalOrder(TotalOrder):
            def __init__(inst, *args, **kwargs):
                super().__init__(*args, **kwargs)
                inst.name = f"{self.name}_<="

        x, y = Variable("x"), Variable("y")
        if strict_total_order is None:
            if total_order is None:
                self.strict_total_order = _CustomStrictTotalOrder
                self.total_order = _CustomTotalOrder
            elif isinstance(total_order(x, y), LessOrEqual):
                self.total_order = total_order
                self.strict_total_order = LessThan
            elif isinstance(total_order(x, y), GreaterOrEqual):
                self.total_order = total_order
                self.strict_total_order = GreaterThan
            else:
                self.total_order = total_order
                self.strict_total_order = _CustomStrictTotalOrder
        else:  # strict_total_order is not None
            self.strict_total_order = strict_total_order
            if total_order is None and isinstance(strict_total_order(x, y), LessThan):
                self.total_order = LessOrEqual
            elif total_order is None and isinstance(
                strict_total_order(x, y), GreaterThan
            ):
                self.total_order = GreaterOrEqual
            elif total_order is None:
                self.total_order = _CustomTotalOrder
            else:
                self.total_order = total_order


F = OrderedField("F")
print(F.strict_order_is_irreflexive)
