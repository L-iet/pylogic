from __future__ import annotations
from typing import TYPE_CHECKING, Literal, TypedDict, TypeVarTuple, Generic, Self
from pylogic.inference import Inference
from pylogic.proposition.proposition import Proposition, get_assumptions
from pylogic.proposition.not_ import neg


if TYPE_CHECKING:
    from pylogic.proposition.and_ import And
    from pylogic.structures.sets import Set
    from pylogic.variable import Variable
    from pylogic.symbol import Symbol
    from sympy import Basic

    Term = Symbol | Set | Basic | int | float
    Unification = dict[Variable, Term]
Tactic = TypedDict("Tactic", {"name": str, "arguments": list[str]})

Ps = TypeVarTuple("Ps")
Props = tuple[Proposition, ...]


class _Junction(Proposition, Generic[*Ps]):
    def __init__(
        self,
        _join_symbol: str,
        *propositions: *Ps,
        is_assumption: bool = False,
        description: str = "",
        _supports_resolve: bool = False,
        **kwargs,
    ) -> None:
        assert len(propositions) > 1, "Must have at least two propositions"
        self.propositions = propositions
        name = f" { _join_symbol } ".join([p.name for p in propositions])  # type: ignore
        super().__init__(name, is_assumption, description=description, **kwargs)
        self.is_atomic = False
        self._join_symbol = _join_symbol
        self._supports_resolve = _supports_resolve
        self.bound_vars: set[Variable] = set()
        for prop in propositions:
            self.bound_vars = self.bound_vars.union(prop.bound_vars)  # type: ignore

    def __eq__(self, other: Proposition) -> bool:
        if isinstance(other, self.__class__):
            return set(self.propositions) == set(other.propositions)
        return False

    def __hash__(self) -> int:
        return hash((self._join_symbol, *self.propositions))

    def copy(self) -> Self:
        return self.__class__(
            *[p.copy() for p in self.propositions],  # type: ignore
            is_assumption=self.is_assumption,
            description=self.description,
            _is_proven=self._is_proven,
            _assumptions=self.from_assumptions,
            _inference=self.deduced_from,
        )

    def as_text(self, *, _indent=0) -> str:
        """
        Return a text representation of the proposition.
        """
        s = ""
        for i, p in enumerate(self.propositions):
            s += p.as_text(_indent=_indent + 1)  # type: ignore
            if i != len(self.propositions) - 1:
                s += "  " * _indent + f"{self._join_symbol}\n"
        return s

    def describe(self, *, _indent=0) -> str:
        """
        Return a description of the proposition.
        """
        if self.description:
            return "  " * _indent + self.description + "\n"
        s = ""
        for i, p in enumerate(self.propositions):
            s += p.describe(_indent=_indent + 1)  # type: ignore
            if i != len(self.propositions) - 1:
                s += "  " * _indent + f"{self._join_symbol}\n"
        return s

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
        new_p = self.__class__(
            *[
                p.replace(current_val, new_val, prop_positions)  # type: ignore
                for p, prop_positions in zip(self.propositions, prop_positions_lists)
            ],
            _is_proven=False,
        )
        return new_p

    def remove_duplicates(self) -> _Junction:
        """
        Remove duplicate propositions from the _junction.
        Returns an equivalent proposition.
        """
        added = set()
        props = []
        for prop in self.propositions:
            if prop not in added:
                props.append(prop)
                added.add(prop)
        new_p = self.__class__(
            *props,
            is_assumption=self.is_assumption,
            description=self.description,
            _is_proven=self._is_proven,
            _assumptions=self.from_assumptions,
            _inference=self.deduced_from,
        )
        return new_p

    def __repr__(self) -> str:
        if self._join_symbol == "or":
            join_symbol = r" \/ "
        elif self._join_symbol == "and":
            join_symbol = r" /\ "
        elif self._join_symbol == "xor":
            join_symbol = " xor "
        else:
            join_symbol = self._join_symbol
        s = join_symbol.join([repr(p) for p in self.propositions])
        return f"({s})"

    def _latex(self, printer=None) -> str:
        if self._join_symbol == "or":
            join_symbol = r"\vee "
        elif self._join_symbol == "and":
            join_symbol = r"\wedge "
        elif self._join_symbol == "xor":
            join_symbol = r"\oplus "
        else:
            join_symbol = rf"{self._join_symbol} \ "
        s = join_symbol.join([p._latex() for p in self.propositions])  # type: ignore
        return rf"\left({s}\right)"

    def unify(self, other: Self) -> Unification | Literal[True] | None:
        if not isinstance(other, self.__class__):
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

    def resolve(self, p: list[Proposition] | And[*Props]) -> Proposition | Self:
        r"""
        Logical tactic. Given self is proven, and p is proven, where p is
        a conjunction or list of negations of propositions in self,
        return a proven disjunction of the remaining propositions in self.

        Given `A \/ B \/ C \/ D` and `~A /\ ~B`, return `C \/ D`.
        """
        if not self._supports_resolve:
            raise NotImplementedError(f"{self} does not support resolution")

        assert self.is_proven, f"{self} is not proven"
        from pylogic.proposition.contradiction import Contradiction
        from pylogic.proposition.and_ import And

        p_is_and = isinstance(p, And)
        props = set(p.propositions if p_is_and else p)
        self_props = self.propositions
        if p_is_and:
            assert p.is_proven, f"{p} is not proven"
            p_assumptions = get_assumptions(p)
        else:
            assert isinstance(p, list), f"{p} is not a list"
            p_assumptions: set[Proposition] = set()
            for prop in props:
                assert prop.is_proven, f"{prop} is not proven"
                p_assumptions = p_assumptions.union(get_assumptions(prop))

        rem_props = [
            self_prop.copy() for self_prop in self_props if neg(self_prop) not in props  # type: ignore
        ]
        if len(rem_props) == 1:
            rem_props[0]._is_proven = True
            rem_props[0].from_assumptions = get_assumptions(self).union(p_assumptions)
            rem_props[0].deduced_from = Inference(self, *props, rule="resolve")
            return rem_props[0]
        if len(rem_props) == 0:
            return Contradiction(
                _is_proven=True,
                _inference=Inference(self, *props, rule="resolve"),
                _assumptions=get_assumptions(self).union(p_assumptions),
            )
        return self.__class__(
            *rem_props,
            _is_proven=True,
            _inference=Inference(self, *props, rule="resolve"),
            _assumptions=get_assumptions(self).union(p_assumptions),
        )

    def unit_resolve(self, p: Proposition) -> Proposition | Self:
        """
        Logical tactic. Given self is proven, and p is proven, where p is
        a negation of one of the propositions in self, return a proven disjunction
        of the remaining propositions in self.
        """
        return self.resolve([p])
