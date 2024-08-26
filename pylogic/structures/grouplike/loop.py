from __future__ import annotations
from typing import Callable, Iterable, TypeVar, TYPE_CHECKING
from fractions import Fraction
from pylogic.structures.set_ import Set
from pylogic.structures.grouplike.quasigroup import Quasigroup
from pylogic.infix.infix import SpecialInfix
from pylogic.expressions.expr import BinaryExpression, Expr
from pylogic.symbol import Symbol
from pylogic.constant import Constant
from pylogic.proposition.and_ import And
from pylogic.proposition.quantified.forall import ForallInSet
from pylogic.proposition.relation.equals import Equals

from sympy import Basic
from sympy import Set as SympySet

Numeric = Fraction | int | float
PBasic = Symbol | Numeric
Unevaluated = Symbol | Set | Expr
Term = Unevaluated | Numeric | Basic

T = TypeVar("T", bound=Term)

if TYPE_CHECKING:
    from pylogic.proposition.relation.contains import IsContainedIn


class Loop(Quasigroup):
    has_identity: And[IsContainedIn, ForallInSet[And[Equals, Equals]]]
    identity_is_given: Equals | None

    @classmethod
    def property_has_identity(
        cls,
        set_: Set,
        operation: SpecialInfix[
            Term, Term, BinaryExpression[Term], BinaryExpression[Term]
        ],
        identity: Term,
    ) -> And[IsContainedIn, ForallInSet[And[Equals, Equals]]]:
        from pylogic.structures.grouplike.monoid import Monoid

        return Monoid.property_has_identity(set_, operation, identity)

    def __init__(
        self,
        name: str | None = None,
        sympy_set: SympySet | None = None,
        elements: Iterable[T] | None = None,
        containment_function: Callable[[T], bool] | None = None,
        operation: Callable[[T, T], T] | None = None,
        operation_name: str | None = None,
        operation_symbol: str | None = None,
        identity: T | None = None,
    ):
        if elements is not None and identity is not None:
            assert identity in elements, "Identity must be in the set of elements"
        super().__init__(
            name,
            sympy_set,
            elements,
            containment_function,
            operation,
            operation_name,
            operation_symbol,
        )
        self.identity = Constant(f"{self.name}_Ident")
        self.identity_is_given = (
            Equals(self.identity, identity, is_axiom=True)
            if identity is not None
            else None
        )
        self.has_identity = Loop.property_has_identity(
            self, self.operation, self.identity
        )
        self.has_identity.is_axiom = True

    def containment_function(self, x: Term) -> bool:
        return x == self.identity or self._containment_function(x)
