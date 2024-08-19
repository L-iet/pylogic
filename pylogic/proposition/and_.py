from __future__ import annotations
from pylogic.inference import Inference
from pylogic.proposition._junction import _Junction
from pylogic.proposition.proposition import Proposition
from pylogic.proposition.proposition import get_assumptions
from typing import TypedDict, TypeVarTuple, Self, TYPE_CHECKING, Union, Unpack, cast

if TYPE_CHECKING:
    from pylogic.proposition.not_ import Not
    from pylogic.proposition.or_ import Or

Tactic = TypedDict("Tactic", {"name": str, "arguments": list[str]})

Ps = TypeVarTuple("Ps")
Props = tuple[Proposition, ...]


class And(_Junction[*Ps]):
    tactics: list[Tactic] = [
        {"name": "all_proven", "arguments": []},
        {"name": "de_morgan", "arguments": []},
    ]

    def __init__(
        self,
        *propositions: *Ps,
        is_assumption: bool = False,
        description: str = "",
        **kwargs,
    ) -> None:
        super().__init__(
            "and",
            *propositions,
            is_assumption=is_assumption,
            description=description,
            _supports_resolve=False,
            **kwargs,
        )

    def __hash__(self) -> int:
        return super().__hash__()

    def __getitem__(self, index: int):
        """
        We get the proposition at the given index.
        Will prove that proposition if self is proven.
        """
        if self.is_proven:
            new_p = self.propositions[index]
            # have to bypass pylance to get Union[*Ps] to work
            if not TYPE_CHECKING:
                new_p = new_p.copy()
            new_p._is_proven = True  # type: ignore
            new_p.deduced_from = Inference(new_p, self, rule="is_one_of")  # type: ignore
            new_p.from_assumptions = get_assumptions(self)  # type: ignore
            return new_p
        return self.propositions[index]  # type: ignore

    def __iter__(self):
        return iter(self.extract())

    def extract(self):
        """
        Will prove all propositions if self is proven.
        """
        if self.is_proven:
            new_props: tuple[*Ps] = [p.copy() for p in self.propositions]  # type: ignore
            for p in new_props:
                p._is_proven = True  # type: ignore
                p.deduced_from = Inference(p, self, rule="is_one_of")  # type: ignore
                p.from_assumptions = get_assumptions(self)  # type: ignore
            return new_props
        return self.propositions

    def de_nest(self) -> And[*tuple[Proposition, ...]]:
        """
        Return a new And proposition with the same propositions as self,
        but without nested And propositions.
        """
        return self.propositions[0].and_(*self.propositions[1:])  # type: ignore

    def remove_duplicates(self) -> And:
        return super().remove_duplicates()  # type: ignore

    def all_proven(self) -> Self:
        """Logical tactic. If all propositions are proven, the conjunction is
        proven."""
        for p in self.propositions:
            if not p.is_proven:  # type: ignore
                raise ValueError(f"{p} is not proven")
        new_p = self.copy()
        new_p._is_proven = True
        new_p.deduced_from = Inference(self, rule="all_proven")
        new_p.from_assumptions = get_assumptions(self).union(get_assumptions(p))  # type: ignore
        return new_p

    def de_morgan(self) -> Not[Or[*Props]]:
        """Apply De Morgan's law to the conjunction to get an
        equivalent proposition."""
        from pylogic.proposition.not_ import neg, Not
        from pylogic.proposition.or_ import Or

        negs: list[Proposition] = [
            neg(p.de_morgan()) for p in self.propositions  # type:ignore
        ]
        return Not(
            Or(*negs),  # type:ignore
            _is_proven=self.is_proven,
            _assumptions=get_assumptions(self),
            _inference=Inference(self, rule="de_morgan"),
        )
