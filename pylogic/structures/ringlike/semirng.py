from __future__ import annotations

from fractions import Fraction
from typing import Callable, Iterable, TypeAlias, TypeVar

from sympy import Basic
from sympy import Set as SympySet

from pylogic.expressions.expr import BinaryExpression, Expr
from pylogic.infix.infix import SpecialInfix
from pylogic.proposition.quantified.forall import ForallInSet
from pylogic.proposition.relation.equals import Equals
from pylogic.structures.grouplike.group import AbelianGroup
from pylogic.structures.ringlike.crooked_semirng import CrookedSemirng
from pylogic.structures.set_ import Set
from pylogic.symbol import Symbol

Numeric = Fraction | int | float
PBasic = Symbol | Numeric
Unevaluated = Symbol | Set | Expr
Term = Unevaluated | Numeric | Basic

T = TypeVar("T", bound=Term)
Z = TypeVar("Z", str, int, float, complex, Fraction)
BinOpFunc: TypeAlias = Callable[[T, T], BinaryExpression[T]]


class Semirng(CrookedSemirng[Z]):
    plus_is_commutative: ForallInSet[ForallInSet[Equals]]

    @classmethod
    def property_plus_is_commutative(
        cls,
        set_: Set,
        plus_operation: SpecialInfix[
            Term, Term, BinaryExpression[Term], BinaryExpression[Term]
        ],
    ) -> ForallInSet[ForallInSet[Equals]]:
        return AbelianGroup.property_op_is_commutative(set_, plus_operation)

    def __init__(
        self,
        name: str | None = None,
        sympy_set: SympySet | None = None,
        elements: Iterable[T] | None = None,
        containment_function: Callable[[T], bool] | None = None,
        plus_operation: Callable[[T, T], T] | None = None,
        plus_operation_symbol: str | None = None,
        zero: Z | Unevaluated | None = None,
        times_operation: Callable[[T, T], T] | None = None,
        times_operation_symbol: str | None = None,
    ):
        super().__init__(
            name=name,
            sympy_set=sympy_set,
            elements=elements,
            containment_function=containment_function,
            plus_operation=plus_operation,
            plus_operation_symbol=plus_operation_symbol,
            zero=zero,
            times_operation=times_operation,
            times_operation_symbol=times_operation_symbol,
        )
        self.plus_is_commutative = Semirng.property_plus_is_commutative(
            self, self.plus_operation
        )
        self.plus_is_commutative.is_axiom = True
