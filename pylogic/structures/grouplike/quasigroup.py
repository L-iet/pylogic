from __future__ import annotations
from typing import Callable, Iterable, TypeVar
from fractions import Fraction
from pylogic.structures.set_ import Set
from pylogic.structures.grouplike.magma import Magma
from pylogic.infix.infix import SpecialInfix
from pylogic.expressions.expr import BinaryExpression, Expr
from pylogic.symbol import Symbol
from pylogic.variable import Variable
from pylogic.proposition.and_ import And
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
    latin_square: ForallInSet[
        ForallInSet[And[ExistsUniqueInSet[Equals], ExistsUniqueInSet[Equals]]]
    ]

    @classmethod
    def property_latin_square(
        cls,
        set_: Set,
        operation: SpecialInfix[
            Term, Term, BinaryExpression[Term], BinaryExpression[Term]
        ],
    ) -> ForallInSet[
        ForallInSet[And[ExistsUniqueInSet[Equals], ExistsUniqueInSet[Equals]]]
    ]:
        r"""
        The Latin square property states that, for each a and b in Q,
        there exist unique elements x and y in Q such that both

        a * x = b

        y * a = b

        Then x = a \ b (left divide) and y = b / a (right divide)
        """
        x = Variable("x")
        a = Variable("a")
        y = Variable("y")
        b = Variable("b")
        a_op_x = a | operation | x

        # the Latin square property states that, for each a and b in Q,
        # there exist unique elements x and y in Q such that both
        # a * x = b
        # y * a = b
        # Then x = a \ b (left divide) and y = b / a (right divide)
        return ForallInSet(
            a,
            set_,
            ForallInSet(
                b,
                set_,
                ExistsUniqueInSet(
                    x,
                    set_,
                    Equals(a_op_x, b),
                ).and_(
                    ExistsUniqueInSet(
                        y,
                        set_,
                        Equals(y | operation | a, b),
                    ),
                ),
            ),
            description=f"For each a and b in {set_.name}, there exist unique x \
and y in {set_.name} such that a {a_op_x.symbol} x = b and y {a_op_x.symbol} a = b",
        )

    def __init__(
        self,
        name: str | None = None,
        sympy_set: SympySet | None = None,
        elements: Iterable[T] | None = None,
        containment_function: Callable[[T], bool] | None = None,
        operation: Callable[[T, T], T] | None = None,
        operation_name: str | None = None,
        operation_symbol: str | None = None,
    ):
        super().__init__(
            name,
            sympy_set,
            elements,
            containment_function,
            operation,
            operation_name,
            operation_symbol,
        )

        self.latin_square = Quasigroup.property_latin_square(self, self.operation)
        self.latin_square.is_axiom = True
