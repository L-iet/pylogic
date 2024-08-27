from __future__ import annotations

from fractions import Fraction
from typing import Callable, Generic, Iterable, TypeAlias, TypeVar

from sympy import Basic
from sympy import Set as SympySet

from pylogic.constant import Constant
from pylogic.expressions.expr import BinaryExpression, Expr
from pylogic.helpers import is_numeric
from pylogic.infix.infix import SpecialInfix
from pylogic.proposition.and_ import And
from pylogic.proposition.quantified.forall import ForallInSet
from pylogic.proposition.relation.contains import IsContainedIn
from pylogic.proposition.relation.equals import Equals
from pylogic.structures.grouplike.monoid import Monoid
from pylogic.structures.grouplike.semigroup import Semigroup
from pylogic.structures.ringlike.ringoid import Ringoid
from pylogic.structures.set_ import Set
from pylogic.symbol import Symbol
from pylogic.variable import Variable

Numeric = Fraction | int | float
PBasic = Symbol | Numeric
Unevaluated = Symbol | Set | Expr
Term = Unevaluated | Numeric | Basic

T = TypeVar("T", bound=Term)
E = TypeVar("E", bound=Expr)
Z = TypeVar("Z", str, int, float, complex, Fraction)
BinOpFunc: TypeAlias = Callable[[T, T], BinaryExpression[T]]


class CrookedSemirng(Ringoid, Generic[Z]):
    zero: Constant[Z] | Unevaluated  # type: ignore
    plus_is_associative: ForallInSet[ForallInSet[ForallInSet[Equals]]]
    plus_has_identity: And[IsContainedIn, ForallInSet[And[Equals, Equals]]]
    times_is_associative: ForallInSet[ForallInSet[ForallInSet[Equals]]]
    zero_mul_eq_zero: ForallInSet[And[Equals, Equals]]

    @classmethod
    def property_plus_is_associative(
        cls,
        set_: Set,
        plus_operation: SpecialInfix[Term, Term, Expr, Expr],
    ) -> ForallInSet[ForallInSet[ForallInSet[Equals]]]:
        return Semigroup.property_op_is_associative(set_, plus_operation)

    @classmethod
    def property_plus_has_identity(
        cls,
        set_: Set,
        plus_operation: SpecialInfix[Term, Term, Expr, Expr],
        zero: Term,
    ) -> And[IsContainedIn, ForallInSet[And[Equals, Equals]]]:
        return Monoid.property_has_identity(set_, plus_operation, zero)

    @classmethod
    def property_times_is_associative(
        cls,
        set_: Set,
        times_operation: SpecialInfix[Term, Term, Expr, Expr],
    ) -> ForallInSet[ForallInSet[ForallInSet[Equals]]]:
        return Semigroup.property_op_is_associative(set_, times_operation)

    @classmethod
    def property_zero_mul_eq_zero(
        cls,
        set_: Set,
        times_operation: SpecialInfix[Term, Term, Expr, Expr],
        zero: Term,
    ) -> ForallInSet[And[Equals, Equals]]:
        x = Variable("x")
        return ForallInSet(
            x,
            set_,
            Equals(zero | times_operation | x, zero).and_(
                Equals(x | times_operation | zero, zero)
            ),
            description=f"{zero} times any element on any side in {set_.name} is {zero}",
        )

    def __init__(
        self,
        name: str | None = None,
        sympy_set: SympySet | None = None,
        elements: Iterable[T] | None = None,
        containment_function: Callable[[T], bool] | None = None,
        plus_operation: Callable[[T, T], E] | None = None,
        plus_operation_symbol: str | None = None,
        zero: Z | Unevaluated | None = None,
        times_operation: Callable[[T, T], E] | None = None,
        times_operation_symbol: str | None = None,
    ):
        super().__init__(
            name=name,
            sympy_set=sympy_set,
            elements=elements,
            containment_function=containment_function,
            plus_operation=plus_operation,
            plus_operation_symbol=plus_operation_symbol,
            times_operation=times_operation,
            times_operation_symbol=times_operation_symbol,
        )
        if is_numeric(zero):
            self.zero: Constant[Z] = Constant(zero)  # type: ignore
        else:
            self.zero: Unevaluated = zero or Constant(f"{self.name}_Zero")  # type: ignore

        self.monoid_plus = Monoid(
            name=name,
            sympy_set=sympy_set,
            elements=elements,
            containment_function=containment_function,  # type: ignore
            operation=plus_operation,  # type: ignore
            operation_name=self.plus_operation_name,
            operation_symbol=self.plus_operation_symbol,
            identity=self.zero,
        )
        self.semigroup_times = Semigroup(
            name=name,
            sympy_set=sympy_set,
            elements=elements,
            containment_function=containment_function,  # type: ignore
            operation=times_operation,  # type: ignore
            operation_name=self.times_operation_name,
            operation_symbol=self.times_operation_symbol,
        )
        self.plus_is_associative = self.monoid_plus.op_is_associative
        self.plus_has_identity = self.monoid_plus.has_identity
        self.times_is_associative = self.semigroup_times.op_is_associative
        self.zero_mul_eq_zero = CrookedSemirng.property_zero_mul_eq_zero(
            self, self.times_operation, self.zero
        )
        self.zero_mul_eq_zero.is_axiom = True
