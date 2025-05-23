from __future__ import annotations

from typing import Callable, Iterable, TypeVar

from pylogic.constant import Constant
from pylogic.expressions.expr import Expr
from pylogic.helpers import is_python_numeric
from pylogic.infix.infix import SpecialInfix
from pylogic.proposition.and_ import And
from pylogic.proposition.quantified.forall import ForallInSet
from pylogic.proposition.relation.contains import IsContainedIn
from pylogic.proposition.relation.equals import Equals
from pylogic.structures.grouplike.semigroup import Semigroup
from pylogic.structures.set_ import Set
from pylogic.symbol import Symbol
from pylogic.typing import Term
from pylogic.variable import Variable

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
        name: str,
        elements: Iterable[T] | None = None,
        containment_function: Callable[[T], bool] | None = None,
        operation: Callable[[T, T], E] | None = None,
        operation_name: str | None = None,
        operation_symbol: str | None = None,
        identity: T | None = None,
        **kwargs,
    ):
        if elements is not None and identity is not None:
            assert identity in elements, "Identity must be in the set of elements"
        Semigroup.__init__(
            self,
            name=name,
            elements=elements,
            containment_function=containment_function,
            operation=operation,
            operation_name=operation_name,
            operation_symbol=operation_symbol,
            **kwargs,
        )
        self._init_args = (name,)
        self._init_kwargs = {
            "elements": elements,
            "containment_function": containment_function,
            "operation": operation,
            "operation_name": operation_name,
            "operation_symbol": operation_symbol,
            "identity": identity,
        }
        self._init_kwargs.update(kwargs)
        if is_python_numeric(identity):
            identity = Constant(identity)  # type: ignore
        self.identity: Symbol | Constant | Set | Expr = identity or Constant(
            f"{self.operation_name}_Ident"
        )  # type: ignore

        self.has_identity = Monoid.property_has_identity(
            self, self.operation, self.identity
        )
        self.has_identity._set_is_axiom(True)

    def containment_function(self, x: Term) -> bool:
        return x == self.identity or super().containment_function(x)
