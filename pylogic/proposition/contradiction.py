from __future__ import annotations
from pylogic.inference import Inference
from pylogic.proposition.proposition import Proposition
from typing import TYPE_CHECKING, Literal, TypeVar, Generic, Self, overload, TypedDict
from sympy.printing.latex import LatexPrinter

latex_printer = LatexPrinter()

if TYPE_CHECKING:
    from pylogic.proposition.implies import Implies
    from pylogic.variable import Variable
    from pylogic.symbol import Symbol
    from pylogic.structures.sets import Set
    from sympy import Basic
    from pylogic.proposition.or_ import Or

    Term = Symbol | Set | Basic | int | float
    Unification = dict[Variable, Term]

TProposition = TypeVar("TProposition", bound="Proposition")
UProposition = TypeVar("UProposition", bound="Proposition")
Tactic = TypedDict("Tactic", {"name": str, "arguments": list[str]})


class Contradiction(Proposition):
    tactics: list[Tactic] = []

    def __init__(self, **kwargs) -> None:
        assert (
            len(kwargs.get("_assumptions", [])) > 1
        ), "A contradiction must have multiple assumptions"
        super().__init__(
            "contradiction",
            is_assumption=False,
            description="contradiction",
            **kwargs,
        )
        self.is_atomic = True

    def __eq__(self, other: Contradiction) -> bool:
        return isinstance(other, Contradiction)

    def copy(self) -> Self:
        return self.__class__()

    def thus_assumptions_cannot_all_hold(self) -> Or[Proposition, ...]:
        """
        Logical tactic. Given a contradiction, return the disjunction of the
        negations of the assumptions.
        """
        from pylogic.proposition.or_ import Or
        from pylogic.proposition.not_ import neg

        return Or(
            *[neg(a) for a in self.from_assumptions],
            description="A contradiction was derived. Therefore, the assumptions cannot all hold.",
            _is_proven=True,
            _assumptions=self.from_assumptions,
            _inference=Inference(self, rule="thus_assumptions_cannot_all_hold"),
        )
