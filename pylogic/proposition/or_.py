from __future__ import annotations
from pylogic.proposition.proposition import Proposition
from pylogic.proposition.not_ import are_negs
from typing import (
    TYPE_CHECKING,
    Literal,
    TypeVar,
    TypedDict,
    TypeVarTuple,
    Generic,
    Self,
    cast,
)

if TYPE_CHECKING:
    from pylogic.set.sets import Set
    from pylogic.variable import Variable
    from pylogic.symbol import Symbol
    from sympy import Basic

    Term = Variable | Symbol | Set | Basic | int | float
    Unification = dict[Variable, Term]
from sympy.printing.latex import LatexPrinter

latex_printer = LatexPrinter()
TProposition = TypeVar("TProposition", bound="Proposition")
Props = TypeVarTuple("Props")
Tactic = TypedDict("Tactic", {"name": str, "arguments": list[str]})


class Or(Proposition, Generic[*Props]):
    tactics: list[Tactic] = [
        {"name": "unit_resolve", "arguments": ["Proposition"]},
        {"name": "one_proven", "arguments": ["Proposition"]},
        {"name": "de_morgan", "arguments": []},
    ]

    def __init__(
        self,
        *propositions: *Props,
        is_assumption: bool = False,
        _is_proven: bool = False,
    ) -> None:
        assert len(propositions) > 1, "'Or' must have at least two propositions"
        self.propositions = propositions
        name = r" \/ ".join([p.name for p in propositions])  # type: ignore
        super().__init__(name, is_assumption, _is_proven=_is_proven)
        self.is_atomic = False

    def __eq__(self, other: Proposition) -> bool:
        if isinstance(other, Or):
            return set(self.propositions) == set(other.propositions)
        return False

    def __hash__(self) -> int:
        return hash(("or", *self.propositions))

    def copy(self) -> Self:
        return self.__class__(
            *[p.copy() for p in self.propositions], is_assumption=self.is_assumption  # type: ignore
        )

    def replace(
        self,
        current_val: Term,
        new_val: Term,
        positions: list[list[int]] | None = None,
    ) -> Self:
        if positions is not None:
            prop_positions_lists = [
                [p[1:] for p in positions if p[0] == i]
                for i in range(len(self.propositions))
            ]
            prop_positions_lists = list(
                map(lambda x: None if [] in x else x, prop_positions_lists)
            )
        else:
            prop_positions_lists = [None] * len(self.propositions)
        new_p = self.copy()
        new_p.propositions = [
            p.replace(current_val, new_val, prop_positions)  # type: ignore
            for p, prop_positions in zip(new_p.propositions, prop_positions_lists)
        ]
        new_p._is_proven = False
        return new_p

    def __repr__(self) -> str:
        s = r" \/ ".join([repr(p) for p in self.propositions])
        return f"({s})"

    def _latex(self, printer=latex_printer) -> str:
        s = r"\vee ".join([p._latex() for p in self.propositions])
        return rf"\left({s}\right)"

    def unit_resolve(self, p: Proposition) -> Proposition | Self:
        """
        Logical tactic. Given self is proven, and p is proven, where p is
        a negation of one of the propositions in self, return a proven disjunction
        of the remaining propositions in self.
        """
        assert self.is_proven, f"{self} is not proven"
        assert p.is_proven, f"{p} is not proven"
        rem_props = [prop.copy() for prop in self.propositions if not are_negs(prop, p)]  # type: ignore
        if len(rem_props) == 1:
            rem_props[0]._is_proven = True
            return rem_props[0]
        return Or(*rem_props, _is_proven=True)  # type: ignore

    def one_proven(self, p: Proposition) -> Self:
        """
        Logical tactic. Given one proven proposition in self, return
        a proof of self (disjunction).
        """
        assert p.is_proven, f"{p} is not proven"
        assert p in self.propositions, f"{p} is not present in {self}"
        new_p = self.copy()
        new_p._is_proven = True
        return new_p

    def de_morgan(self) -> Proposition:
        """Apply De Morgan's law to the disjunction to get an
        equivalent proposition."""
        from pylogic.proposition.not_ import neg, Not
        from pylogic.proposition.and_ import And

        negs: list[Proposition] = [
            neg(p.de_morgan()) for p in self.propositions  # type:ignore
        ]
        return Not(And(*negs), _is_proven=self.is_proven)

    def unify(self, other: Self) -> Unification | Literal[True] | None:
        if not isinstance(other, Or):
            raise TypeError(
                f"{other} is not an instance of {self.__class__}\n\
Occured when trying to unify `{self}` and `{other}`"
            )
        if len(self.propositions) != len(other.propositions):
            return None
        d: Unification = {}
        for s_prop, o_prop in zip(self.propositions, other.propositions):
            res: Unification | Literal[True] | None = s_prop.unify(o_prop)  # type: ignore
            if res is None:
                return None
            if isinstance(res, dict):
                for k in res:
                    if k in d and d[k] != res[k]:
                        return None
                    d[k] = res[k]
        if len(d) == 0:
            return True
        else:
            return d
