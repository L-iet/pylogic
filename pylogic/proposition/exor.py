from __future__ import annotations

from typing import TYPE_CHECKING, Self, TypedDict, TypeVarTuple

from pylogic.inference import Inference
from pylogic.proposition._junction import _Junction
from pylogic.proposition.not_ import neg
from pylogic.proposition.proposition import Proposition, get_assumptions

if TYPE_CHECKING:
    from pylogic.proposition.and_ import And

Ps = TypeVarTuple("Ps")
Tactic = TypedDict("Tactic", {"name": str, "arguments": list[str]})
Props = tuple[Proposition, ...]


class ExOr(_Junction[*Ps]):
    tactics: list[Tactic] = [
        {"name": "one_proven", "arguments": ["Proposition"]},
    ]
    _supports_resolve = True
    _supports_by_cases = True

    def __init__(
        self,
        *propositions: *Ps,
        is_assumption: bool = False,
        description: str = "",
        **kwargs,
    ) -> None:
        super().__init__(
            "xor",
            *propositions,
            is_assumption=is_assumption,
            description=description,
            **kwargs,
        )

    def __hash__(self) -> int:
        return super().__hash__()

    def remove_duplicates(self) -> ExOr:
        return super().remove_duplicates()  # type: ignore

    def one_proven_rem_false(self, p: Proposition) -> And[*Props]:
        """
        Logical tactic. Given self is proven, and one proven proposition in self,
        return a proof that all the remaining propositions are false.
        """
        assert self.is_proven, f"{self} is not proven"
        assert p.is_proven, f"{p} is not proven"
        assert p in self.propositions, f"{p} is not present in {self}"
        from pylogic.proposition.and_ import And

        rem_props = [prop for prop in self.propositions if prop != p]
        new_p = And(
            *[neg(prop) for prop in rem_props],  # type: ignore
            _is_proven=True,
            _assumptions=get_assumptions(self).union(get_assumptions(p)),
            _inference=Inference(self, p, rule="one_proven_rem_false"),
        )
        return new_p

    def one_proven(self, p: Proposition) -> Self:
        """
        Logical tactic. Given one proven proposition in self, return
        a proof of self (exclusive or).
        """
        assert p.is_proven, f"{p} is not proven"
        assert p in self.propositions, f"{p} is not present in {self}"
        new_p = self.copy()
        new_p._is_proven = True
        new_p.deduced_from = Inference(self, p, rule="one_proven")
        new_p.from_assumptions = get_assumptions(self).union(get_assumptions(p))
        return new_p
