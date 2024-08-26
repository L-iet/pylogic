from __future__ import annotations

from fractions import Fraction
from typing import Callable, Iterable, TypeAlias, TypeVar

from sympy import Basic
from sympy import Set as SympySet

from pylogic.expressions.expr import BinaryExpression, Expr
from pylogic.infix.infix import SpecialInfix
from pylogic.proposition.and_ import And
from pylogic.proposition.quantified.exists import ExistsUniqueInSet
from pylogic.proposition.quantified.forall import ForallInSet
from pylogic.proposition.relation.equals import Equals
from pylogic.structures.grouplike.group import AbelianGroup, Group
from pylogic.structures.ringlike.semiring import SemirIng
from pylogic.structures.set_ import Set
from pylogic.symbol import Symbol

Numeric = Fraction | int | float
PBasic = Symbol | Numeric
Unevaluated = Symbol | Set | Expr
Term = Unevaluated | Numeric | Basic

T = TypeVar("T", bound=Term)
Z = TypeVar("Z", str, int, float, complex, Fraction)
BinOpFunc: TypeAlias = Callable[[T, T], BinaryExpression[T]]


class RIng(SemirIng[Z]):
    have_add_inverses: ForallInSet[ExistsUniqueInSet[And[Equals, Equals]]]
    plus_latin_square = ForallInSet[
        ForallInSet[And[ExistsUniqueInSet[Equals], ExistsUniqueInSet[Equals]]]
    ]

    @classmethod
    def property_have_add_inverses(
        cls,
        set_: Set,
        plus_operation: SpecialInfix[
            Term, Term, BinaryExpression[Term], BinaryExpression[Term]
        ],
        zero: Term,
    ) -> ForallInSet[ExistsUniqueInSet[And[Equals, Equals]]]:
        return Group.property_have_inverses(set_, plus_operation, zero)

    @classmethod
    def property_plus_latin_square(
        cls,
        set_: Set,
        plus_operation: SpecialInfix[
            Term, Term, BinaryExpression[Term], BinaryExpression[Term]
        ],
    ) -> ForallInSet[
        ForallInSet[And[ExistsUniqueInSet[Equals], ExistsUniqueInSet[Equals]]]
    ]:
        return Group.property_latin_square(set_, plus_operation)

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
        one: Z | Unevaluated | None = None,
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
            one=one,
        )
        self.abelian_group_plus = AbelianGroup(
            name=name,
            sympy_set=sympy_set,
            elements=elements,
            containment_function=containment_function,  # type: ignore
            operation=plus_operation,  # type: ignore
            operation_name=self.plus_operation_name,
            operation_symbol=self.plus_operation_symbol,
            identity=self.zero,
        )
        self.have_add_inverses = self.abelian_group_plus.have_inverses
        self.plus_latin_square = self.abelian_group_plus.latin_square
