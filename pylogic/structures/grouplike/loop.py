from __future__ import annotations

from typing import TYPE_CHECKING, Callable, Iterable, TypeVar

from pylogic.constant import Constant
from pylogic.expressions.expr import Expr
from pylogic.helpers import is_python_numeric
from pylogic.infix.infix import SpecialInfix
from pylogic.proposition.and_ import And
from pylogic.proposition.quantified.forall import ForallInSet
from pylogic.proposition.relation.equals import Equals
from pylogic.structures.grouplike.quasigroup import Quasigroup
from pylogic.structures.set_ import Set
from pylogic.symbol import Symbol
from pylogic.typing import Term

T = TypeVar("T", bound=Term)
E = TypeVar("E", bound=Expr)

if TYPE_CHECKING:
    from pylogic.proposition.relation.contains import IsContainedIn


class Loop(Quasigroup):
    has_identity: And[IsContainedIn, ForallInSet[And[Equals, Equals]]]

    @classmethod
    def property_has_identity(
        cls,
        set_: Set,
        operation: SpecialInfix[Term, Term, Expr, Expr],
        identity: Term,
    ) -> And[IsContainedIn, ForallInSet[And[Equals, Equals]]]:
        from pylogic.structures.grouplike.monoid import Monoid

        return Monoid.property_has_identity(set_, operation, identity)

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
        Quasigroup.__init__(
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

        self.has_identity = Loop.property_has_identity(
            self, self.operation, self.identity
        )
        self.has_identity._set_is_axiom(True)

    def containment_function(self, x: Term) -> bool:
        return x == self.identity or super().containment_function(x)
