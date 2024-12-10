from __future__ import annotations

from typing import TYPE_CHECKING, Any, cast, overload

from pylogic.symbol import Symbol
from pylogic.typing import Term

if TYPE_CHECKING:
    from pylogic.assumptions_context import AssumptionsContext
    from pylogic.expressions.sequence_term import SequenceTerm
    from pylogic.proposition.quantified.exists import Exists
    from pylogic.proposition.relation.contains import IsContainedIn
else:
    AssumptionsContext = Any
    Exists = Any
    IsContainedIn = Any


class Variable(Symbol):
    def __init__(self, *args, depends_on: tuple[Variable, ...] = (), **kwargs) -> None:
        super().__init__(*args, depends_on=depends_on, **kwargs)
        self.kwargs = self.kwargs + [
            ("bound", "is_bound"),
            ("elements", "elements"),
            ("empty", "is_empty"),
            ("cartes_power", "is_cartes_power"),
            ("cartes_product", "is_cartes_product"),
            ("finite", "is_finite"),
            ("intersection", "is_intersection"),
            ("union", "is_union"),
            ("context", "dummy"),
        ]

    def __new_init__(
        self, *args, depends_on: tuple[Variable, ...] = (), **kwargs
    ) -> None:
        context = cast(AssumptionsContext | None, kwargs.get("context", None))
        # append to context first before appending its
        # other assumptions
        if context is not None:
            context.assumptions.append(self)

        super().__new_init__(*args, depends_on=depends_on, **kwargs)
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
        self.is_intersection: bool | None = None
        self.is_union: bool | None = None

        # for variable sequences
        self.nth_term = None

    def __contains__(self, item: Any) -> bool:
        """
        For variable sets.
        """
        return item in self.elements

    def containment_function(self, x: Term) -> bool:
        """
        For variable sets.
        """
        return x in self.elements

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

    def countable(self, is_assumption: bool = False, **kwargs) -> Exists:
        # for variable sets
        # TODO: make this  ExistsInSet where set is the class of
        # all sequences
        from pylogic.proposition.quantified.exists import Exists
        from pylogic.structures.set_ import SeqSet
        from pylogic.variable import Variable

        s = Variable("s", sequence=True)
        return Exists(
            s,
            self.equals(SeqSet(s)),
            description=f"{self} is countable",
            is_assumption=is_assumption,
            **kwargs,
        )

    def __getitem__(self, index: Term) -> SequenceTerm:
        # for variable sequences
        from pylogic.expressions.sequence_term import SequenceTerm

        return SequenceTerm(self, index)

    def unbind(self) -> None:
        self.is_bound = False


def unbind(*variables: Variable) -> None:
    """Unbinds variables. This indicates that they are no longer bound to a
    quantifier and can be reused in nested quantified statements.
    """
    for variable in variables:
        variable.unbind()


@overload
def variables(name: str, **kwargs) -> Variable: ...
@overload
def variables(*names: str, **kwargs) -> tuple[Variable, ...]: ...
def variables(*names: str, **kwargs) -> Variable | tuple[Variable, ...]:
    """Creates variables."""
    if len(names) == 1:
        return Variable(names[0], **kwargs)
    return tuple(Variable(name, **kwargs) for name in names)


Var = Variable
