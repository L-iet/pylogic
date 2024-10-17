from __future__ import annotations

from typing import TYPE_CHECKING, Any

from pylogic import Term
from pylogic.symbol import Symbol

if TYPE_CHECKING:
    from pylogic.proposition.relation.contains import IsContainedIn


class Variable(Symbol):
    def __init__(self, *args, depends_on: tuple[Variable, ...] = (), **kwargs) -> None:
        super().__init__(*args, depends_on=depends_on, **kwargs)
        self.is_bound: bool = False
        # if the variable is created from a proven existential statement
        # it won't be equal to any other constant
        self._from_existential_instance = kwargs.pop(
            "_from_existential_instance", False
        )
        # for variable sets
        self.elements = set()
        self.is_empty: bool | None = None
        self.is_cartes_power: bool | None = None
        self.is_cartes_product: bool | None = None
        self.is_finite: bool | None = None
        self.is_intersection: bool | None = None
        self.is_union: bool | None = None

    def __contains__(self, item: Any) -> bool:
        """
        For variable sets.
        """
        return item in self.elements

    def predicate(self, x: Term) -> IsContainedIn:
        """
        For variable sets.
        """
        from pylogic.proposition.relation.contains import IsContainedIn

        return IsContainedIn(x, self)

    def contains(self, x: Term, **kwargs) -> IsContainedIn:
        """
        For variable sets.
        """
        return IsContainedIn(x, self, **kwargs)

    def unbind(self) -> None:
        self.is_bound = False


def unbind(*variables: Variable) -> None:
    """Unbinds variables. This indicates that they are no longer bound to a
    quantifier and can be reused in nested quantified statements.
    """
    for variable in variables:
        variable.unbind()


def variables(*names: str, **kwargs) -> list[Variable]:
    """Creates a list of variables with the given names."""
    return [Variable(name, **kwargs) for name in names]


Var = Variable
