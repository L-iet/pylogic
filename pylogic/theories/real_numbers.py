from __future__ import annotations

from fractions import Fraction
from typing import (
    TYPE_CHECKING,
    Any,
    Callable,
    Generic,
    Iterable,
    TypeAlias,
    TypeVar,
    cast,
)

from pylogic import Term, Unevaluated
from pylogic.constant import Constant
from pylogic.expressions.expr import Add, Mul
from pylogic.proposition.and_ import And
from pylogic.proposition.implies import Implies
from pylogic.proposition.not_ import Not
from pylogic.proposition.ordering.lessorequal import LessOrEqual
from pylogic.proposition.ordering.lessthan import LessThan
from pylogic.proposition.quantified.exists import ExistsInSet, ExistsUniqueInSet
from pylogic.proposition.quantified.forall import ForallInSet, ForallSubsets
from pylogic.proposition.relation.equals import Equals
from pylogic.proposition.relation.subsets import IsSubsetOf
from pylogic.structures.ordered_set import OrderedSet
from pylogic.structures.ringlike.field import Field
from pylogic.structures.set_ import Set
from pylogic.variable import Variable

zero = Constant(0)
one = Constant(1)

if TYPE_CHECKING:
    from pylogic.expressions.expr import BinaryExpression, Expr
    from pylogic.proposition.ordering.total import StrictTotalOrder, TotalOrder
    from pylogic.proposition.relation.contains import IsContainedIn

    IsUpperBound = ForallInSet[LessOrEqual]
    IsLowerBound = ForallInSet[LessOrEqual]
    BoundedAbove = ExistsInSet[IsUpperBound]
    BoundedBelow = ExistsInSet[IsLowerBound]
    HasLUB = ExistsUniqueInSet[
        And[IsUpperBound, ForallInSet[Implies[IsUpperBound, LessOrEqual]]]
    ]
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


class RealsField(Field[Z], OrderedSet):

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
    ) -> ForallSubsets[
        Implies[
            And[Not[Equals], BoundedAbove],
            HasLUB,
        ]
    ]:
        from pylogic.structures.set_ import EmptySet

        s = Variable("s", set_=True)
        return ForallSubsets(
            s,
            set_,
            Not(s.equals(EmptySet))
            .and_(set_.bounded_above(s))
            .implies(set_.has_lub(s)),
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
            **kwargs,
        }

        self.bounded_above_has_lub = RealsField.property_bounded_above_has_lub(self)
        self.bounded_above_has_lub._set_is_axiom(True)
        self.less_than = LessThan
        self.less_or_equal = LessOrEqual

    def is_ub(self, ub, s) -> IsUpperBound:
        x = Variable("x")
        return ForallInSet(
            x,
            s,
            self.total_order(x, ub),
            description=f"{ub} is an upper bound of {s}",
        )  # type:ignore

    def bounded_above(self, s) -> BoundedAbove:
        ub = Variable("ub")
        return ExistsInSet(
            ub,
            self,
            self.is_ub(ub, s),
            description=f"{s} is bounded above",
        )

    def has_lub(self, s) -> HasLUB:
        lub = Variable("lub")
        y = Variable("y")
        return ExistsUniqueInSet(
            lub,
            self,
            self.is_ub(lub, s).and_(
                ForallInSet(
                    y,
                    self,
                    self.is_ub(y, s).implies(self.total_order(lub, y)),
                )
            ),
            description=f"{s} has a least upper bound",
        )


Reals = RealsField(
    "Reals",
    plus_operation=Add,
    plus_operation_symbol="+",
    times_operation=Mul,
    times_operation_symbol="*",
    containment_function=lambda x: getattr(x, "is_real", False),
    zero=zero,
    one=one,
    total_order=LessOrEqual,
    strict_total_order=LessThan,
    latex_name="\\mathbb{R}",
)


class Interval(Set):
    def __init__(
        self, a: T, b: T, a_inclusive: bool = False, b_inclusive: bool = False
    ):
        from pylogic.helpers import python_to_pylogic
        from pylogic.inference import Inference
        from pylogic.proposition.ordering.lessorequal import LessOrEqual
        from pylogic.proposition.ordering.lessthan import LessThan

        a, b = python_to_pylogic(a), python_to_pylogic(b)  # type:ignore

        left_symb = "[" if a_inclusive else "("
        right_symb = "]" if b_inclusive else ")"
        left_pred = LessOrEqual if a_inclusive else LessThan
        right_pred = LessOrEqual if b_inclusive else LessThan
        pred = lambda x: And(x.is_in(Reals), left_pred(a, x), right_pred(x, b))
        super().__init__(
            f"{left_symb}{a},{b}{right_symb}",
            predicate=pred,
        )
        self.a = a
        self.b = b
        self.a_inclusive = self.a._is_in_by_rule(self) if a_inclusive else None
        self.b_inclusive = self.b._is_in_by_rule(self) if b_inclusive else None
        self.is_subset_of_reals = IsSubsetOf(
            self,
            Reals,
            _is_proven=True,
            _inference=Inference(None, rule="by_definition"),
        )
        self.knowledge_base.add(self.is_subset_of_reals)

    def evaluate(self):
        from pylogic.structures.set_ import EmptySet, FiniteSet

        if self.a == self.b:
            if self.a_inclusive and self.b_inclusive:
                return FiniteSet(self.name, {self.a})
            return EmptySet
        return self