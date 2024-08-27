from __future__ import annotations

from fractions import Fraction
from typing import TYPE_CHECKING, Callable, Generic, Iterable, TypeVar

from sympy import Basic
from sympy import Set as SympySet

from pylogic.expressions.expr import BinaryExpression, Expr
from pylogic.infix.infix import SpecialInfix
from pylogic.proposition.quantified.forall import ForallInSet
from pylogic.proposition.relation.contains import IsContainedIn
from pylogic.structures.set_ import Set
from pylogic.symbol import Symbol
from pylogic.variable import Variable

Numeric = Fraction | int | float
PBasic = Symbol | Numeric
Unevaluated = Symbol | Set | Expr
Term = Unevaluated | Numeric | Basic

T = TypeVar("T", bound=Term)
E = TypeVar("E", bound=Expr)


class Magma(Set):
    is_closed_under_op: ForallInSet[ForallInSet[IsContainedIn]]

    # TODO: if operation.symbol is None, this will look weird
    @classmethod
    def property_is_closed_under_op(
        cls,
        set_: Set,
        operation: SpecialInfix[Term, Term, Expr, Expr],
    ) -> ForallInSet[ForallInSet[IsContainedIn]]:
        x = Variable("x")
        y = Variable("y")
        x_op_y = x | operation | y
        return ForallInSet(
            x,
            set_,
            ForallInSet(y, set_, IsContainedIn(x_op_y, set_)),
            description=f"{set_.name} is closed under the operation {operation.symbol}",
        )

    def __init__(
        self,
        name: str | None = None,
        sympy_set: SympySet | None = None,
        elements: Iterable[T] | None = None,
        containment_function: Callable[[T], bool] | None = None,
        operation: Callable[[T, T], E] | None = None,
        operation_name: str | None = None,
        operation_symbol: str | None = None,
    ):
        # TODO: need to check that the set is closed under the operation
        # make this functionality optional
        super().__init__(name, sympy_set, elements, containment_function)  # type: ignore
        self.operation_name = operation_name or f"{self.name}_Op"
        self.operation_symbol = operation_symbol or f"{self.name}_Op"
        bin_op_func = operation or (
            lambda x, y: BinaryExpression(
                self.operation_name, self.operation_symbol, x, y, None
            )
        )
        self.operation: SpecialInfix[Term, Term, Expr, Expr] = SpecialInfix(
            operate=bin_op_func,
            call=bin_op_func,
            symbol=self.operation_symbol,
        )  # type: ignore
        self.op = self.operation
        self.is_closed_under_op = Magma.property_is_closed_under_op(
            self, self.operation
        )
        self.is_closed_under_op.is_axiom = True

    def containment_function(self, x: Term) -> bool:
        if isinstance(x, BinaryExpression):
            return (
                x.name == self.operation_name
                and x.symbol == self.operation_symbol
                and all(self.containment_function(arg) for arg in x.args)
            )
        return self._containment_function(x)
