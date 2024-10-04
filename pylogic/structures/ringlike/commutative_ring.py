from __future__ import annotations

from fractions import Fraction
from typing import Callable, Iterable, TypeAlias, TypeVar

from pylogic import Term, Unevaluated
from pylogic.expressions.expr import BinaryExpression, Expr
from pylogic.infix.infix import SpecialInfix
from pylogic.proposition.quantified.forall import ForallInSet
from pylogic.proposition.relation.equals import Equals
from pylogic.structures.grouplike.group import AbelianGroup
from pylogic.structures.ringlike.ring import RIng
from pylogic.structures.set_ import Set
from pylogic.symbol import Symbol

T = TypeVar("T", bound=Term)
E = TypeVar("E", bound=Expr)
Z = TypeVar("Z", str, int, float, complex, Fraction)
BinOpFunc: TypeAlias = Callable[[T, T], BinaryExpression[T]]


class CommutativeRIng(RIng[Z]):
    times_is_commutative: ForallInSet[ForallInSet[Equals]]

    @classmethod
    def property_times_is_commutative(
        cls,
        set_: Set,
        times_operation: SpecialInfix[Term, Term, Expr, Expr],
    ) -> ForallInSet[ForallInSet[Equals]]:
        return AbelianGroup.property_op_is_commutative(set_, times_operation)

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
        self.times_is_commutative = CommutativeRIng.property_times_is_commutative(
            self, self.times_operation
        )
        self.times_is_commutative._set_is_axiom(True)
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
