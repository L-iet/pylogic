from __future__ import annotations
from typing import Callable, TYPE_CHECKING, Iterable, Generic, TypeVar
from pylogic.structures.sets import Set
from pylogic.infix.infix import SpecialInfix
from pylogic.expressions.expr import BinaryExpression

from fractions import Fraction
from pylogic.symbol import Symbol
from pylogic.expressions.expr import Expr

from sympy import Basic
from sympy import Set as SympySet

Numeric = Fraction | int | float
PBasic = Symbol | Numeric
Unevaluated = Symbol | Set | Expr
Term = Unevaluated | Numeric | Basic

T = TypeVar("T", bound=Term)


class Group(Set, Generic[T]):
    def __init__(
        self,
        name: str | None = None,
        sympy_set: SympySet | None = None,
        elements: Iterable[T] | None = None,
        containment_function: Callable[[T], bool] | None = None,
        operation: Callable[[T, T], T] | None = None,
        operation_symbol: str | None = None,
    ):
        # TODO: need to check that the operation is associative
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
        self._contains = self.containment_function
        del self.containment_function

    def containment_function(self, x: Term) -> bool:
        if isinstance(x, BinaryExpression):
            return (
                x.name == self.operation_name
                and x.symbol == self.operation_symbol
                and all(self.containment_function(arg) for arg in x.args)
            )
        return self._contains(x)
