from __future__ import annotations

from abc import ABC, abstractmethod
from typing import (
    TYPE_CHECKING,
    Callable,
    Generic,
    Literal,
    Self,
    TypedDict,
    TypeVar,
    TypeVarTuple,
)

from pylogic import Term, Unification
from pylogic.helpers import find_first
from pylogic.inference import Inference
from pylogic.proposition.not_ import neg
from pylogic.proposition.proposition import Proposition, get_assumptions

if TYPE_CHECKING:
    from pylogic.proposition.and_ import And
    from pylogic.proposition.implies import Implies
    from pylogic.structures.class_ import Class
    from pylogic.structures.set_ import Set
    from pylogic.symbol import Symbol
    from pylogic.variable import Variable

Tactic = TypedDict("Tactic", {"name": str, "arguments": list[str]})

T = TypeVar("T", bound="_Junction")

Ps = TypeVarTuple("Ps")
Props = tuple[Proposition, ...]


class _Junction(Proposition, Generic[*Ps], ABC):
    _distributes_over_: set[str] = set()
    _supports_resolve: bool = False
    _supports_by_cases: bool = False

    def __init__(
        self,
        _join_symbol: str,
        *propositions: *Ps,
        is_assumption: bool = False,
        description: str = "",
        **kwargs,
    ) -> None:
        assert len(propositions) > 1, "Must have at least two propositions"
        self.propositions = propositions
        name = f" { _join_symbol } ".join([p.name for p in propositions])  # type: ignore
        super().__init__(name, is_assumption, description=description, **kwargs)
        self.is_atomic = False
        self._join_symbol = _join_symbol
        self.bound_vars: set[Variable] = set()
        self.variables: set[Variable] = set()
        self.constants: set[Symbol] = set()
        self.sets: set[Set] = set()
        self.class_ns: set[Class] = set()
        for prop in propositions:
            self.bound_vars = self.bound_vars.union(prop.bound_vars)  # type: ignore
            self.variables = self.variables.union(prop.variables)  # type: ignore
            self.constants = self.constants.union(prop.constants)  # type: ignore
            self.sets = self.sets.union(prop.sets)  # type: ignore
            self.class_ns = self.class_ns.union(prop.class_ns)  # type: ignore

        self._idx = 0  # for iteration over propositions

    def __eq__(self, other: Proposition) -> bool:
        if isinstance(other, self.__class__):
            return set(self.propositions) == set(other.propositions)
        return False

    def __hash__(self) -> int:
        return hash((self._join_symbol, *self.propositions))

    def __getitem__(self, index: int):
        return self.propositions[index]

    def __iter__(self):
        return iter(self.propositions)

    def __next__(self):
        try:
            item = self[self._idx]
        except IndexError:
            raise StopIteration()
        self._idx += 1
        return item

    def _distributes_over(self, other: str) -> bool:
        """
        return True if self distributes over other, else False
        """
        return other in self._distributes_over_

    def copy(self) -> Self:
        return self.__class__(
            *self.propositions,  # type: ignore
            is_assumption=self.is_assumption,
            description=self.description,
            _is_proven=self._is_proven,
            _assumptions=self.from_assumptions,
            _inference=self.deduced_from,
        )

    def deepcopy(self) -> Self:
        return self.__class__(
            *[p.deepcopy() for p in self.propositions],  # type: ignore
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
        equal_check: Callable | None = None,
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
                p.replace(current_val, new_val, prop_positions, equal_check=equal_check)  # type: ignore
                for p, prop_positions in zip(self.propositions, prop_positions_lists)
            ],
            _is_proven=False,
        )
        return new_p

    def remove_duplicates(self) -> _Junction | Proposition:
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
        if len(props) == 1:
            return props[0]
        new_p = self.__class__(
            *props,  # type: ignore
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
        from pylogic.proposition.and_ import And
        from pylogic.proposition.contradiction import Contradiction

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
            self_prop for self_prop in self_props if neg(self_prop) not in props  # type: ignore
        ]
        if len(rem_props) == 1:
            rem_prop = rem_props[0].copy()  # type: ignore
            rem_prop._set_is_proven(True)
            rem_prop.from_assumptions = get_assumptions(self).union(p_assumptions)
            rem_prop.deduced_from = Inference(self, *props, rule="resolve")  # type: ignore
            return rem_prop
        if len(rem_props) == 0:
            return Contradiction(
                _is_proven=True,
                _inference=Inference(self, *props, rule="resolve"),  # type: ignore
                _assumptions=get_assumptions(self).union(p_assumptions),
            )
        return self.__class__(
            *rem_props,  # type: ignore
            _is_proven=True,
            _inference=Inference(self, *props, rule="resolve"),  # type: ignore
            _assumptions=get_assumptions(self).union(p_assumptions),
        )

    def by_cases(self, *implications: Implies[Proposition, Proposition]) -> Proposition:
        r"""
        Logical tactic.
        If self is of the form `A \/ B \/ C...`, and there are implications
        `A -> D`, `B -> E`, `C -> F...`, return `D \/ E \/ F...`.
        """
        assert self._supports_by_cases, f"{self} does not support by_cases"
        assert self.is_proven, f"{self} is not proven"
        antes = [imp.antecedent for imp in implications]
        assert len(antes) == len(
            self.propositions
        ), "Not all cases or too many cases (Number of implications must match)"
        assert set(antes) == set(
            self.propositions
        ), "Implications (cases) must match propositions in disjunction"
        new_p = self.__class__(
            *[imp.consequent for imp in implications],  # type: ignore
            _is_proven=True,
            _assumptions=get_assumptions(self).union(
                *[get_assumptions(imp) for imp in implications]
            ),
            _inference=Inference(self, *implications, rule="by_cases"),
        ).remove_duplicates()
        return new_p

    def unit_resolve(self, p: Proposition) -> Proposition | Self:
        """
        Logical tactic. Given self is proven, and p is proven, where p is
        a negation of one of the propositions in self, return a proven disjunction
        of the remaining propositions in self.
        """
        return self.resolve([p])

    def has_as_subproposition(self, other: Proposition) -> bool:
        """
        Check if other is a subproposition of self.
        """
        if self == other:
            return True
        _, first_other_occurs_in = find_first(
            lambda p: p.has_as_subproposition(other), self.propositions  # type: ignore
        )
        return first_other_occurs_in is not None

    def de_nest(self) -> _Junction[*tuple[Proposition, ...]]:
        """
        Return a new _Junction proposition with the same propositions as self,
        but without nested propositions of the same type.
        """
        props = []
        for p in self.propositions:
            if isinstance(p, self.__class__):
                props.extend(p.de_nest().propositions)
            else:
                props.append(p)
        return self.__class__(
            *props,  # type: ignore
            description=self.description,
            _is_proven=self.is_proven,
            _assumptions=self.from_assumptions,
            _inference=Inference(self, rule="de_nest"),
        )

    def left_distribute(self) -> Proposition:
        r"""
        Logical tactic. Return an equivalent proposition
        that is the result of left distribution.
        For example, if self is `A \/ (B /\ C)`, return `(A \/ B) /\ (A \/ C)`.
        """
        assert len(self.propositions) == 2, f"{self} must have two propositions"
        other_junc: Proposition = self.propositions[1]  # type: ignore
        other_cls_name = other_junc.__class__.__name__
        assert self._distributes_over(
            other_cls_name
        ), f"{self.__class__.__name__} does not distribute over {other_cls_name}"
        new_props = [self.__class__(self.propositions[0], p) for p in other_junc.propositions]  # type: ignore
        new_p = other_junc.__class__(
            *new_props,  # type: ignore
            description=self.description,
            _is_proven=self.is_proven,
            _assumptions=get_assumptions(self),
            _inference=Inference(self, rule="left_distribute"),
        )
        return new_p

    def right_distribute(self) -> Proposition:
        r"""
        Logical tactic. Return an equivalent proposition
        that is the result of right distribution.
        For example, if self is `(A /\ B) \/ C`, return `(A \/ C) /\ (B \/ C)`.
        """
        assert len(self.propositions) == 2, f"{self} must have two propositions"
        other_junc: Proposition = self.propositions[0]  # type: ignore
        other_cls_name = other_junc.__class__.__name__
        assert self._distributes_over(
            other_cls_name
        ), f"{self.__class__.__name__} does not distribute over {other_cls_name}"
        new_props = [self.__class__(p, self.propositions[1]) for p in other_junc.propositions]  # type: ignore
        new_p = other_junc.__class__(
            *new_props,  # type: ignore
            description=self.description,
            _is_proven=self.is_proven,
            _assumptions=get_assumptions(self),
            _inference=Inference(self, rule="right_distribute"),
        )
        return new_p

    def distribute(self) -> Proposition:
        """
        Logical tactic. Return an equivalent proposition
        that is the result of distribution.
        Defaults to left distribution unless not possible.
        """
        try:
            return self.left_distribute()
        except AssertionError:
            return self.right_distribute()
