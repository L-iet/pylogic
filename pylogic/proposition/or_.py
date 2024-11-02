from __future__ import annotations

from typing import TYPE_CHECKING, Self, TypedDict, TypeVarTuple

from pylogic.inference import Inference
from pylogic.proposition._junction import _Junction
from pylogic.proposition.proposition import Proposition, get_assumptions

if TYPE_CHECKING:
    pass

Ps = TypeVarTuple("Ps")
InferenceRule = TypedDict("InferenceRule", {"name": str, "arguments": list[str]})
Props = tuple[Proposition, ...]


class Or(_Junction[*Ps]):
    # order of operations for propositions (0-indexed)
    # not xor and or => <=> forall forallInSet forallSubsets exists existsInSet existsUnique
    # existsUniqueInSet existsSubset existsUniqueSubset Proposition
    _precedence = 3

    _inference_rules: list[InferenceRule] = [
        {"name": "unit_resolve", "arguments": ["Proposition"]},
        {"name": "one_proven", "arguments": ["Proposition"]},
        {"name": "de_morgan", "arguments": []},
        {"name": "resolve", "arguments": ["Proposition"]},
        {"name": "unit_resolve", "arguments": ["Proposition"]},
        {"name": "by_cases", "arguments": []},
        {"name": "left_distribute", "arguments": []},
        {"name": "right_distribute", "arguments": []},
        {"name": "distribute", "arguments": []},
    ]

    _distributes_over_ = {"And"}
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
            "or",
            *propositions,
            is_assumption=is_assumption,
            description=description,
            **kwargs,
        )

    def __hash__(self) -> int:
        return super().__hash__()

    def __getitem__(self, index: int) -> Proposition:
        return self.propositions[index]  # type: ignore

    def __iter__(self):
        return iter(self.propositions)

    def remove_duplicates(self) -> Or:
        return super().remove_duplicates()  # type: ignore

    def one_proven(self, p: Proposition) -> Self:
        """
        Logical inference rule. Given one proven proposition in self, return
        a proof of self (disjunction).
        """
        assert p.is_proven, f"{p} is not proven"
        assert p in self.propositions, f"{p} is not present in {self}"
        new_p = self.copy()
        new_p._set_is_proven(True)
        new_p.deduced_from = Inference(self, p, rule="one_proven")
        new_p.from_assumptions = get_assumptions(self).union(get_assumptions(p))
        return new_p

    def de_morgan(self) -> Proposition:
        """
        Logical inference rule.
        Apply De Morgan's law to the disjunction to get an
        equivalent proposition.

        In intuitionistic logic, the only valid De Morgan's laws are

        `~A and ~B <-> ~(A or B)`

        `~A or ~B -> ~(A and B)`.
        """
        from pylogic.enviroment_settings.settings import settings
        from pylogic.proposition.and_ import And
        from pylogic.proposition.not_ import Not, neg

        if settings["USE_CLASSICAL_LOGIC"] == False:
            if not all(isinstance(p, Not) for p in self.propositions):
                return self
            return Not(
                And(*[p.negated.de_morgan() for p in self.propositions]),
                _is_proven=self.is_proven,
                _assumptions=get_assumptions(self),
                _inference=Inference(self, rule="de_morgan"),
            )

        negs: list[Proposition] = [
            neg(p.de_morgan()) for p in self.propositions  # type:ignore
        ]
        return Not(
            And(*negs),  # type: ignore
            description=self.description,
            _is_proven=self.is_proven,
            _assumptions=get_assumptions(self),
            _inference=Inference(self, rule="de_morgan"),
        )
