from __future__ import annotations

from fractions import Fraction
from typing import TYPE_CHECKING, Any, Callable, Iterable, Self, TypeAlias, TypeVar

from pylogic import Term, Unevaluated
from pylogic.constant import Constant
from pylogic.expressions.expr import Add, Mul
from pylogic.expressions.function import Function
from pylogic.proposition.ordering.lessorequal import LessOrEqual
from pylogic.proposition.ordering.lessthan import LessThan
from pylogic.proposition.proposition import Proposition
from pylogic.proposition.quantified.exists import ExistsInSet
from pylogic.structures.ordered_set import OrderedSet
from pylogic.structures.ringlike.ring import RIng
from pylogic.variable import Variable

zero = Constant(0)
one = Constant(1)

if TYPE_CHECKING:
    from pylogic.expressions.expr import BinaryExpression, Expr
    from pylogic.proposition.ordering.total import StrictTotalOrder, TotalOrder
    from pylogic.proposition.relation.divides import Divides

    T = TypeVar("T", bound=Term)
    E = TypeVar("E", bound=Expr)
    Z = TypeVar("Z", str, int, float, complex, Fraction)

    BinOpFunc: TypeAlias = Callable[[T, T], BinaryExpression[T]]
    TotalOrderOp: TypeAlias = Callable[..., TotalOrder]
    StrictTotalOrderOp: TypeAlias = Callable[..., StrictTotalOrder]
else:
    Term = Any
    Unevaluated = Any
    T = Any
    E = Any
    Z = Any
    BinOpFunc = Any
    TotalOrderOp = Any
    StrictTotalOrderOp = Any


class IntegersRing(RIng[Z], OrderedSet):
    successor: Function
    predecessor: Function

    # TODO: add weak_induction_formal for integers
    # If M is a set of integers such that
    # (i) M is not empty ; (ii) for every integer x, x is in M if and only if x+1 is in M;
    # then M=Z

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
        RIng.__init__(
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

        self.less_than = LessThan
        self.less_or_equal = LessOrEqual

        x = Variable("x")
        self.successor = Function(
            "Integers.successor", self, self, parameters=(x,), definition=x + 1
        )
        self.predecessor = Function(
            "Integers.predecessor", self, self, parameters=(x,), definition=x - 1
        )

    def divides(self, a: Z, b: Z, **kwargs) -> Divides:
        from pylogic.proposition.relation.divides import Divides

        return Divides(a, b, self, **kwargs)


Integers = IntegersRing(
    "Integers",
    plus_operation=Add,
    plus_operation_symbol="+",
    times_operation=Mul,
    times_operation_symbol="*",
    containment_function=lambda x: getattr(x, "is_integer", False),
    zero=zero,
    one=one,
    total_order=LessOrEqual,
    strict_total_order=LessThan,
    latex_name="\\mathbb{Z}",
)
