from __future__ import annotations

from fractions import Fraction
from typing import Callable, Iterable, TypeAlias, TypeVar

from pylogic.constant import Constant
from pylogic.expressions.expr import BinaryExpression, Expr
from pylogic.helpers import is_python_numeric
from pylogic.infix.infix import SpecialInfix
from pylogic.proposition.and_ import And
from pylogic.proposition.quantified.forall import ForallInSet
from pylogic.proposition.relation.contains import IsContainedIn
from pylogic.proposition.relation.equals import Equals
from pylogic.structures.grouplike.monoid import Monoid
from pylogic.structures.ringlike.semirng import Semirng
from pylogic.structures.set_ import Set
from pylogic.typing import Term, Unevaluated

T = TypeVar("T", bound=Term)
E = TypeVar("E", bound=Expr)
Z = TypeVar("Z", str, int, float, complex, Fraction)
BinOpFunc: TypeAlias = Callable[[T, T], BinaryExpression[T]]


class SemirIng(Semirng[Z]):
    one: Constant[Z] | Unevaluated  # type: ignore
    times_has_identity: And[IsContainedIn, ForallInSet[And[Equals, Equals]]]

    @classmethod
    def property_times_has_identity(
        cls,
        set_: Set,
        times_operation: SpecialInfix[Term, Term, Expr, Expr],
        one: Term,
    ) -> And[IsContainedIn, ForallInSet[And[Equals, Equals]]]:
        return Monoid.property_has_identity(set_, times_operation, one)

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
        **kwargs,
    ):
        Semirng.__init__(
            self,
            name=name,
            elements=elements,
            containment_function=containment_function,
            plus_operation=plus_operation,
            plus_operation_symbol=plus_operation_symbol,
            zero=zero,
            times_operation=times_operation,
            times_operation_symbol=times_operation_symbol,
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
        }
        self._init_kwargs.update(kwargs)
        if is_python_numeric(one):
            self.one: Constant[Z] = Constant(one)  # type: ignore
        else:
            self.one: Unevaluated = one or Constant(f"{self.name}_One")  # type: ignore

        self.monoid_times = Monoid(
            name=name,
            elements=elements,
            containment_function=containment_function,  # type: ignore
            operation=times_operation,  # type: ignore
            operation_name=self.times_operation_name,
            operation_symbol=self.times_operation_symbol,
            identity=self.one,
        )
        self.times_has_identity = self._replace_instance_set(
            self.monoid_times, "has_identity"
        )
