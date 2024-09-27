from fractions import Fraction
from typing import TYPE_CHECKING, Any, Callable, Iterable, TypeAlias, TypeVar

from pylogic.constant import Constant
from pylogic.expressions.expr import Add, Mul
from pylogic.proposition.and_ import And
from pylogic.proposition.implies import Implies
from pylogic.proposition.not_ import Not
from pylogic.proposition.ordering.lessorequal import LessOrEqual
from pylogic.proposition.quantified.exists import ExistsInSet, ExistsUniqueInSet
from pylogic.proposition.quantified.forall import ForallInSet, ForallSubsets
from pylogic.proposition.relation.equals import Equals
from pylogic.proposition.relation.subsets import IsSubsetOf
from pylogic.structures.ringlike.ordered_field import OrderedField
from pylogic.structures.set_ import Set
from pylogic.variable import Variable

zero = Constant(0)
one = Constant(1)

if TYPE_CHECKING:
    from pylogic.expressions.expr import BinaryExpression, Expr
    from pylogic.proposition.ordering.total import StrictTotalOrder, TotalOrder
    from pylogic.symbol import Symbol

    IsUpperBound = ForallInSet[LessOrEqual]
    IsLowerBound = ForallInSet[LessOrEqual]
    BoundedAbove = ExistsInSet[IsUpperBound]
    BoundedBelow = ExistsInSet[IsLowerBound]
    HasLUB = ExistsUniqueInSet[
        And[IsUpperBound, ForallInSet[Implies[IsUpperBound, LessOrEqual]]]
    ]

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
    IsUpperBound = Any
    IsLowerBound = Any
    BoundedAbove = Any
    BoundedBelow = Any
    HasLUB = Any
    Term = Any
    Unevaluated = Any
    T = Any
    E = Any
    Z = Any
    BinOpFunc = Any
    TotalOrderOp = Any
    StrictTotalOrderOp = Any


class RealsField(OrderedField):

    bounded_above_has_lub: ForallSubsets[
        Implies[
            And[Not[Equals], BoundedAbove],
            HasLUB,
        ]
    ]

    @classmethod
    def property_bounded_above_has_lub(
        cls,
        set_: Set,
        total_order: TotalOrderOp,
    ) -> ForallSubsets[
        Implies[
            And[Not[Equals], BoundedAbove],
            HasLUB,
        ]
    ]:
        from pylogic.structures.set_ import EmptySet

        def is_ub(ub, s) -> IsUpperBound:
            x = Variable("x")
            return ForallInSet(
                x,
                s,
                total_order(x, ub),
                description=f"{ub} is an upper bound of {s}",
            )  # type:ignore

        def bounded_above(s) -> BoundedAbove:
            ub = Variable("ub")
            return ExistsInSet(
                ub,
                set_,
                is_ub(ub, s),
                description=f"{s} is bounded above",
            )

        def has_lub(s) -> HasLUB:
            lub = Variable("lub")
            y = Variable("y")
            return ExistsUniqueInSet(
                lub,
                set_,
                is_ub(lub, s).and_(
                    ForallInSet(
                        y,
                        set_,
                        is_ub(y, s).implies(total_order(lub, y)),
                    )
                ),
                description=f"{s} has a least upper bound",
            )

        s = Variable("s", set_=True)
        return ForallSubsets(
            s,
            set_,
            Not(s.equals(EmptySet)).and_(bounded_above(s)).implies(has_lub(s)),
            description=f"Every nonempty subset of {set_} that is bounded above has a least upper bound",
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
            total_order=total_order,
            strict_total_order=strict_total_order,
        )
        self.bounded_above_has_lub = RealsField.property_bounded_above_has_lub(
            self, self.total_order
        )


Reals = RealsField(
    "Reals",
    plus_operation=Add,
    plus_operation_symbol="+",
    times_operation=Mul,
    times_operation_symbol="*",
    zero=zero,
    one=one,
)
