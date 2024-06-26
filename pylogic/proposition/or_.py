from __future__ import annotations
from pylogic.inference import Inference
from pylogic.proposition._junction import _Junction
from pylogic.proposition.proposition import Proposition
from pylogic.proposition.proposition import get_assumptions
from typing import TYPE_CHECKING, TypedDict, TypeVarTuple, Self

if TYPE_CHECKING:
    from pylogic.proposition.and_ import And

Ps = TypeVarTuple("Ps")
Tactic = TypedDict("Tactic", {"name": str, "arguments": list[str]})
Props = tuple[Proposition, ...]


class Or(_Junction[*Ps]):
    tactics: list[Tactic] = [
        {"name": "unit_resolve", "arguments": ["Proposition"]},
        {"name": "one_proven", "arguments": ["Proposition"]},
        {"name": "de_morgan", "arguments": []},
        {"name": "resolve", "arguments": ["Proposition"]},
    ]

    def __init__(
        self,
        *propositions: *Ps,
        is_assumption: bool = False,
        description: str = "",
        **kwargs,
    ) -> None:
        super().__init__(
            "or",
            *propositions,
            is_assumption=is_assumption,
            description=description,
            _supports_resolve=True,
            **kwargs,
        )

    def __hash__(self) -> int:
        return super().__hash__()

    def remove_duplicates(self) -> Or:
        return super().remove_duplicates()  # type: ignore

    def one_proven(self, p: Proposition) -> Self:
        """
        Logical tactic. Given one proven proposition in self, return
        a proof of self (disjunction).
        """
        assert p.is_proven, f"{p} is not proven"
        assert p in self.propositions, f"{p} is not present in {self}"
        new_p = self.copy()
        new_p._is_proven = True
        new_p.deduced_from = Inference(self, p, rule="one_proven")
        new_p.from_assumptions = get_assumptions(self).union(get_assumptions(p))
        return new_p

    def de_morgan(self) -> Proposition:
        """Apply De Morgan's law to the disjunction to get an
        equivalent proposition."""
        from pylogic.proposition.not_ import neg, Not
        from pylogic.proposition.and_ import And

        negs: list[Proposition] = [
            neg(p.de_morgan()) for p in self.propositions  # type:ignore
        ]
        return Not(
            And(*negs),
            description=self.description,
            _is_proven=self.is_proven,
            _assumptions=get_assumptions(self),
            _inference=Inference(self, rule="de_morgan"),
        )
