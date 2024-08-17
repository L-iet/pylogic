from __future__ import annotations
from typing import Callable, TYPE_CHECKING, Iterable
from pylogic.structures.sets import Set
from pylogic.infix.infix import SpecialInfix
from pylogic.expressions.expr import BinaryOperation

if TYPE_CHECKING:
    from fractions import Fraction
    from pylogic.symbol import Symbol
    from pylogic.expressions.expr import Expr

    from sympy import Basic
    from sympy import Set as SympySet

    Numeric = Fraction | int | float
    PBasic = Symbol | Numeric
    Unevaluated = Symbol | Set | Expr
    Term = Unevaluated | Numeric | Basic


class Group(Set):
    def __init__(
        self,
        name: str | None = None,
        sympy_set: SympySet | None = None,
        elements: Iterable[Term] | None = None,
        containment_function: Callable[[Term], bool] | None = None,
        operation: Callable[[Term, Term], Term] | None = None,
        operation_symbol: str | None = None,
    ):
        # TODO: need to check that the operation is associative
        super().__init__(name, sympy_set, elements, containment_function)
        self.operation_name = f"{self.name}_Op"
        self.operation_symbol = operation_symbol or f"{self.name}_Op"
        bin_op_func = lambda x, y: BinaryOperation(
            self.operation_name, self.operation_symbol, x, y, operation
        )
        self.operation: SpecialInfix[
            Term, Term, BinaryOperation[Term], BinaryOperation[Term]
        ] = SpecialInfix(
            operate=bin_op_func,
            call=bin_op_func,
        )
        self.op = self.operation
        self._contains = self.containment_function
        del self.containment_function

    def containment_function(self, x: Term) -> bool:
        if isinstance(x, BinaryOperation):
            return (
                x.name == self.operation_name
                and x.symbol == self.operation_symbol
                and all(self.containment_function(arg) for arg in x.args)
            )
        return self._contains(x)
