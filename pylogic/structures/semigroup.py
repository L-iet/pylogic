from __future__ import annotations
from typing import Callable, Iterable, TypeVar
from fractions import Fraction
from pylogic.structures.set_ import Set
from pylogic.structures.magma import Magma
from pylogic.infix.infix import SpecialInfix
from pylogic.expressions.expr import BinaryExpression, Expr
from pylogic.symbol import Symbol
from pylogic.variable import Variable
from pylogic.proposition.quantified.forall import ForallInSet
from pylogic.proposition.relation.equals import Equals

from sympy import Basic
from sympy import Set as SympySet

Numeric = Fraction | int | float
PBasic = Symbol | Numeric
Unevaluated = Symbol | Set | Expr
Term = Unevaluated | Numeric | Basic

T = TypeVar("T", bound=Term)


class Semigroup(Magma):
    op_is_associative: ForallInSet[ForallInSet[ForallInSet[Equals]]]

    @classmethod
    def property_op_is_associative(
        cls,
        set_: Set,
        operation: SpecialInfix[
            Term, Term, BinaryExpression[Term], BinaryExpression[Term]
        ],
    ) -> ForallInSet[ForallInSet[ForallInSet[Equals]]]:
        x = Variable("x")
        y = Variable("y")
        z = Variable("z")
        x_op_y = x | operation | y
        x_op_y_op_z = x_op_y | operation | z
        return ForallInSet(
            x,
            set_,
            ForallInSet(
                y,
                set_,
                ForallInSet(
                    z,
                    set_,
                    Equals(x_op_y_op_z, x | operation | (y | operation | z)),
                ),
            ),
            description=f"{x_op_y.symbol} is associative in {set_.name}",
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
        super().__init__(
            name, sympy_set, elements, containment_function, operation, operation_symbol
        )
        self.op_is_associative = Semigroup.property_op_is_associative(
            self, self.operation
        )
        self.op_is_associative.is_axiom = True
