from __future__ import annotations

from fractions import Fraction
from typing import Callable, Iterable, TypeVar

from sympy import Basic
from sympy import Set as SympySet

from pylogic.constant import Constant
from pylogic.expressions.expr import BinaryExpression, Expr
from pylogic.helpers import is_numeric
from pylogic.infix.infix import SpecialInfix
from pylogic.proposition.and_ import And
from pylogic.proposition.quantified.forall import ForallInSet
from pylogic.proposition.relation.contains import IsContainedIn
from pylogic.proposition.relation.equals import Equals
from pylogic.structures.grouplike.semigroup import Semigroup
from pylogic.structures.set_ import Set
from pylogic.symbol import Symbol
from pylogic.variable import Variable

Numeric = Fraction | int | float
PBasic = Symbol | Numeric
Unevaluated = Symbol | Set | Expr
Term = Unevaluated | Numeric | Basic

T = TypeVar("T", bound=Term)
E = TypeVar("E", bound=Expr)


class Monoid(Semigroup):
    has_identity: And[IsContainedIn, ForallInSet[And[Equals, Equals]]]

    @classmethod
    def property_has_identity(
        cls,
        set_: Set,
        operation: SpecialInfix[Term, Term, Expr, Expr],
        identity: Term,
    ) -> And[IsContainedIn, ForallInSet[And[Equals, Equals]]]:
        x = Variable("x")
        return And(
            IsContainedIn(identity, set_),
            ForallInSet(
                x,
                set_,
                And(
                    Equals(x | operation | identity, x),
                    Equals(identity | operation | x, x),
                ),
            ),
            description=f"{identity} is the identity element in {set_.name}",
        )

    def __init__(
        self,
        name: str | None = None,
        sympy_set: SympySet | None = None,
        elements: Iterable[T] | None = None,
        containment_function: Callable[[T], bool] | None = None,
        operation: Callable[[T, T], E] | None = None,
        operation_name: str | None = None,
        operation_symbol: str | None = None,
        identity: T | None = None,
    ):
        if elements is not None and identity is not None:
            assert identity in elements, "Identity must be in the set of elements"
        super().__init__(
            name=name,
            sympy_set=sympy_set,
            elements=elements,
            containment_function=containment_function,
            operation=operation,
            operation_name=operation_name,
            operation_symbol=operation_symbol,
        )
        if is_numeric(identity):
            identity = Constant(identity)  # type: ignore
        self.identity: Symbol | Constant | Set | Expr = identity or Constant(
            f"{self.operation_name}_Ident"
        )  # type: ignore

        self.has_identity = Monoid.property_has_identity(
            self, self.operation, self.identity
        )
        self.has_identity.is_axiom = True

    def containment_function(self, x: Term) -> bool:
        return x == self.identity or self._containment_function(x)
