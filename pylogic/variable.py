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
        self.elements = set()  # for variable sets

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
