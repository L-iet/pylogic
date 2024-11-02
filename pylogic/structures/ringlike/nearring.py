from __future__ import annotations

from fractions import Fraction
from typing import Callable, Iterable, TypeAlias, TypeVar

from pylogic import Term, Unevaluated
from pylogic.expressions.expr import BinaryExpression, Expr
from pylogic.infix.infix import SpecialInfix
from pylogic.proposition.and_ import And
from pylogic.proposition.quantified.exists import ExistsUniqueInSet
from pylogic.proposition.quantified.forall import ForallInSet
from pylogic.proposition.relation.equals import Equals
from pylogic.structures.grouplike.group import Group
from pylogic.structures.ringlike.crooked_semiring import CrookedSemirIng
from pylogic.structures.set_ import Set

T = TypeVar("T", bound=Term)
E = TypeVar("E", bound=Expr)
Z = TypeVar("Z", str, int, float, complex, Fraction)
BinOpFunc: TypeAlias = Callable[[T, T], BinaryExpression[T]]


class NearrIng(CrookedSemirIng[Z]):
    have_add_inverses: ForallInSet[ExistsUniqueInSet[And[Equals, Equals]]]
    plus_latin_square = ForallInSet[
        ForallInSet[And[ExistsUniqueInSet[Equals], ExistsUniqueInSet[Equals]]]
    ]

    @classmethod
    def property_have_add_inverses(
        cls,
        set_: Set,
        plus_operation: SpecialInfix[Term, Term, Expr, Expr],
        zero: Term,
    ) -> ForallInSet[ExistsUniqueInSet[And[Equals, Equals]]]:
        return Group.property_have_inverses(set_, plus_operation, zero)

    @classmethod
    def property_plus_latin_square(
        cls,
        set_: Set,
        plus_operation: SpecialInfix[Term, Term, Expr, Expr],
    ) -> ForallInSet[
        ForallInSet[And[ExistsUniqueInSet[Equals], ExistsUniqueInSet[Equals]]]
    ]:
        return Group.property_latin_square(set_, plus_operation)

    def __init__(
        self,
        name: str,
        elements: Iterable[T] | None = None,
        containment_function: Callable[[T], bool] | None = None,
        plus_operation: Callable[[T, T], E] | None = None,
        plus_operation_symbol: str | None = None,
        zero: Z | Unevaluated | None = None,
        times_operation: Callable[[T, T], E] | None = None,
        times_operation_symbol: str | None = None,
        one: Z | Unevaluated | None = None,
        **kwargs,
    ):
        self._init_args = (name,)
        self._init_kwargs = {
            "elements": elements,
            "containment_function": containment_function,
            "plus_operation": plus_operation,
            "plus_operation_symbol": plus_operation_symbol,
            "zero": zero,
            "times_operation": times_operation,
            "times_operation_symbol": times_operation_symbol,
            "one": one,
        }
        self._init_kwargs.update(kwargs)
        CrookedSemirIng.__init__(
            self,
            name=name,
            elements=elements,
            containment_function=containment_function,
            plus_operation=plus_operation,
            plus_operation_symbol=plus_operation_symbol,
            zero=zero,
            times_operation=times_operation,
            times_operation_symbol=times_operation_symbol,
            one=one,
            **kwargs,
        )
        self.group_plus = Group(
            name=name,
            elements=elements,
            containment_function=containment_function,  # type: ignore
            operation=plus_operation,  # type: ignore
            operation_name=self.plus_operation_name,
            operation_symbol=self.plus_operation_symbol,
            identity=self.zero,
        )
        self.have_add_inverses = self._replace_instance_set(
            self.group_plus, "have_inverses"
        )
        self.plus_latin_square = self._replace_instance_set(
            self.group_plus, "latin_square"
        )
