from __future__ import annotations
from typing import Callable, TYPE_CHECKING, Iterable, Generic, TypeVar
from fractions import Fraction
from pylogic.structures.set_ import Set
from pylogic.infix.infix import SpecialInfix
from pylogic.expressions.expr import BinaryExpression, Expr
from pylogic.symbol import Symbol
from pylogic.variable import Variable
from pylogic.proposition.quantified.forall import ForallInSet
from pylogic.proposition.relation.contains import IsContainedIn

from sympy import Basic
from sympy import Set as SympySet

Numeric = Fraction | int | float
PBasic = Symbol | Numeric
Unevaluated = Symbol | Set | Expr
Term = Unevaluated | Numeric | Basic

T = TypeVar("T", bound=Term)


class Magma(Set):
    is_closed_under_op: ForallInSet[ForallInSet[IsContainedIn]]

    @classmethod
    def property_is_closed_under_op(
        cls,
        set_: Set,
        operation: SpecialInfix[
            Term, Term, BinaryExpression[Term], BinaryExpression[Term]
        ],
    ) -> ForallInSet[ForallInSet[IsContainedIn]]:
        x = Variable("x")
        y = Variable("y")
        x_op_y = x | operation | y
        return ForallInSet(
            x,
            set_,
            ForallInSet(y, set_, IsContainedIn(x_op_y, set_)),
            description=f"{set_.name} is closed under the operation {x_op_y.symbol}",
        )

    def __init__(
        self,
        name: str | None = None,
        sympy_set: SympySet | None = None,
        elements: Iterable[T] | None = None,
        containment_function: Callable[[T], bool] | None = None,
        operation: Callable[[T, T], T] | None = None,
        operation_symbol: str | None = None,
    ):
        # TODO: need to check that the set is closed under the operation
        # make this functionality optional
        super().__init__(name, sympy_set, elements, containment_function)  # type: ignore
        self.operation_name = f"{self.name}_Op"
        self.operation_symbol = operation_symbol or f"{self.name}_Op"
        bin_op_func = lambda x, y: BinaryExpression(
            self.operation_name, self.operation_symbol, x, y, operation
        )
        self.operation: SpecialInfix[
            Term, Term, BinaryExpression[Term], BinaryExpression[Term]
        ] = SpecialInfix(
            operate=bin_op_func,
            call=bin_op_func,
        )
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
