from __future__ import annotations

from fractions import Fraction
from typing import Callable, Iterable, TypeAlias, TypeVar

from pylogic import Term, Unevaluated
from pylogic.expressions.expr import BinaryExpression, Expr
from pylogic.infix.infix import SpecialInfix
from pylogic.proposition.and_ import And
from pylogic.proposition.implies import Implies
from pylogic.proposition.or_ import Or
from pylogic.proposition.quantified.exists import ExistsUniqueInSet
from pylogic.proposition.quantified.forall import ForallInSet
from pylogic.proposition.relation.equals import Equals
from pylogic.structures.grouplike.group import Group
from pylogic.structures.ringlike.ring import RIng
from pylogic.structures.set_ import Set
from pylogic.variable import Variable

T = TypeVar("T", bound=Term)
E = TypeVar("E", bound=Expr)
Z = TypeVar("Z", str, int, float, complex, Fraction)
BinOpFunc: TypeAlias = Callable[[T, T], BinaryExpression[T]]


class DivisionRIng(RIng[Z]):
    have_mul_inverses: ForallInSet[ExistsUniqueInSet[And[Equals, Equals]]]
    times_latin_square: ForallInSet[
        ForallInSet[And[ExistsUniqueInSet[Equals], ExistsUniqueInSet[Equals]]]
    ]
    zero_product: ForallInSet[ForallInSet[Implies[Equals, Or[Equals, Equals]]]]

    @classmethod
    def property_have_mul_inverses(
        cls,
        set_: Set,
        times_operation: SpecialInfix[Term, Term, Expr, Expr],
        one: Term,
    ) -> ForallInSet[ExistsUniqueInSet[And[Equals, Equals]]]:
        return Group.property_have_inverses(set_, times_operation, one)

    @classmethod
    def property_times_latin_square(
        cls,
        set_: Set,
        times_operation: SpecialInfix[Term, Term, Expr, Expr],
    ) -> ForallInSet[
        ForallInSet[And[ExistsUniqueInSet[Equals], ExistsUniqueInSet[Equals]]]
    ]:
        return Group.property_latin_square(set_, times_operation)

    @classmethod
    def property_zero_product(
        cls,
        set_: Set,
        times_operation: SpecialInfix[Term, Term, Expr, Expr],
        zero: Term,
    ) -> ForallInSet[ForallInSet[Implies[Equals, Or[Equals, Equals]]]]:
        a = Variable("a")
        b = Variable("b")
        return ForallInSet(
            a,
            set_,
            ForallInSet(
                b,
                set_,
                Implies(
                    Equals(a | times_operation | b, zero),
                    Or(Equals(a, zero), Equals(b, zero)),
                ),
            ),
            description="a*b = 0 implies a = 0 or b = 0",
        )

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
        RIng.__init__(
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
        self.group_times = Group(
            name=name,
            elements=elements,
            containment_function=containment_function,  # type: ignore
            operation=times_operation,  # type: ignore
            operation_name=self.times_operation_name,
            operation_symbol=self.times_operation_symbol,
            identity=one,  # type: ignore
        )
        self.have_mul_inverses = self._replace_instance_set(
            self.group_times, "have_inverses"
        )
        self.times_latin_square = self._replace_instance_set(
            self.group_times, "latin_square"
        )
        self.zero_product = DivisionRIng.property_zero_product(
            set_=self,
            times_operation=self.times_operation,
            zero=self.zero,
        )
        self.zero_product._set_is_axiom(True)
