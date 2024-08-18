from __future__ import annotations
from typing import Callable, Iterable, TypeVar
from fractions import Fraction
from pylogic.structures.set_ import Set
from pylogic.structures.magma import Magma
from pylogic.expressions.expr import Expr
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
        x = Variable("x")
        y = Variable("y")
        z = Variable("z")
        self.op_is_associative = ForallInSet(
            x,
            self,
            ForallInSet(
                y,
                self,
                ForallInSet(
                    z,
                    self,
                    Equals(
                        (x | self.operation | y) | self.operation | z,
                        x | self.operation | (y | self.operation | z),
                    ),
                ),
            ),
            is_axiom=True,
            description=f"{self.operation_name} is associative in {self.name}",
        )
