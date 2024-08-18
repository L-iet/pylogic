from __future__ import annotations
from typing import Callable, Iterable, TypeVar
from fractions import Fraction
from pylogic.structures.set_ import Set
from pylogic.structures.magma import Magma
from pylogic.expressions.expr import Expr
from pylogic.symbol import Symbol
from pylogic.variable import Variable
from pylogic.proposition.quantified.forall import ForallInSet
from pylogic.proposition.quantified.exists import ExistsUniqueInSet
from pylogic.proposition.relation.equals import Equals

from sympy import Basic
from sympy import Set as SympySet

Numeric = Fraction | int | float
PBasic = Symbol | Numeric
Unevaluated = Symbol | Set | Expr
Term = Unevaluated | Numeric | Basic

T = TypeVar("T", bound=Term)


class Quasigroup(Magma):
    # https://en.wikipedia.org/wiki/Quasigroup
    have_inverse: ForallInSet

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
        a = Variable("a")
        y = Variable("y")
        b = Variable("b")

        # the Latin square property states that, for each a and b in Q,
        # there exist unique elements x and y in Q such that both
        # a * x = b
        # y * a = b
        # Then x = a \ b (left divide) and y = b / a (right divide)
        self.latin_square = ForallInSet(
            a,
            self,
            ForallInSet(
                b,
                self,
                ExistsUniqueInSet(
                    x,
                    self,
                    Equals(a | self.operation | x, b),
                ).and_(
                    ExistsUniqueInSet(
                        y,
                        self,
                        Equals(y | self.operation | a, b),
                    ),
                ),
            ),
            is_axiom=True,
            description=f"For each a and b in {name}, there exist unique x and y in {name} such that a {self.operation_symbol} x = b and y {self.operation_symbol} a = b",
        )


Q = Quasigroup("Q")
print(Q.latin_square.describe())
