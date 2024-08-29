# pyright: reportInvalidTypeForm=false
from __future__ import annotations

from typing import TYPE_CHECKING, Self, TypedDict, TypeVar

from pylogic.inference import Inference
from pylogic.proposition.proposition import Proposition

if TYPE_CHECKING:
    from fractions import Fraction

    from pylogic.expressions.expr import Expr
    from pylogic.proposition.or_ import Or
    from pylogic.structures.set_ import Set
    from pylogic.symbol import Symbol
    from pylogic.variable import Variable

    Numeric = Fraction | int | float
    PBasic = Symbol | Numeric
    Unevaluated = Symbol | Set | Expr
    Term = Unevaluated | Numeric
    Unification = dict[Variable, Term]

TProposition = TypeVar("TProposition", bound="Proposition")
UProposition = TypeVar("UProposition", bound="Proposition")
Tactic = TypedDict("Tactic", {"name": str, "arguments": list[str]})


class Contradiction(Proposition):
    tactics: list[Tactic] = [
        {"name": "thus_assumptions_cannot_all_hold", "arguments": []}
    ]
    """
    A contradiction can be assumed.
    """

    def __init__(self, **kwargs) -> None:
        if "_is_proven" in kwargs:
            assert (
                len(kwargs.get("_assumptions", [])) > 1
            ), "A contradiction must have multiple assumptions"
        super().__init__(
            "contradiction",
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
        from pylogic.proposition.not_ import neg
        from pylogic.proposition.or_ import Or

        assert self.is_proven, "This contradiction is not proven"
        return Or(
            *[neg(a) for a in self.from_assumptions],  # type: ignore
            description="",
            _is_proven=True,
            _assumptions=self.from_assumptions,
            _inference=Inference(self, rule="thus_assumptions_cannot_all_hold"),
        )
