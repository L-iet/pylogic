# pyright: reportInvalidTypeForm=false
from __future__ import annotations

from typing import TYPE_CHECKING, Generic, Literal, Self, TypedDict, TypeVar

from pylogic.inference import Inference
from pylogic.proposition.not_ import neg
from pylogic.proposition.proposition import Proposition, get_assumptions

if TYPE_CHECKING:
    from fractions import Fraction


    from pylogic.expressions.expr import Expr
    from pylogic.proposition.and_ import And
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
VProposition = TypeVar("VProposition", bound="Proposition")
Tactic = TypedDict("Tactic", {"name": str, "arguments": list[str]})


class Implies(Proposition, Generic[TProposition, UProposition]):
    tactics: list[Tactic] = [
        {"name": "hypothetical_syllogism", "arguments": ["Implies"]},
        {"name": "impl_elim", "arguments": []},
        {"name": "definite_clause_resolve", "arguments": ["Proposition"]},
    ]

    # TODO: Implement __eq__ for IsContainedIn, Relation, Equals etc
    def __init__(
        self,
        antecedent: TProposition,
        consequent: UProposition,
        is_assumption: bool = False,
        description: str = "",
        **kwargs,
    ) -> None:
        self.antecedent = antecedent
        self.consequent = consequent
        name = f"{antecedent.name} -> {consequent.name}"
        super().__init__(name, is_assumption, description=description, **kwargs)
        self.is_atomic = False
        self.bound_vars = antecedent.bound_vars.union(consequent.bound_vars)

    def __eq__(self, other: Proposition) -> bool:
        if isinstance(other, Implies):
            return (
                self.antecedent == other.antecedent
                and self.consequent == other.consequent
            )
        return False

    def __hash__(self) -> int:
        return hash(("impl", self.antecedent, self.consequent))

    def __repr__(self) -> str:
        return f"[{self.antecedent} -> {self.consequent}]"

    def _latex(self, printer=None) -> str:
        return rf"\left({self.antecedent._latex()} \rightarrow {self.consequent._latex()}\right)"

    def copy(self) -> Self:
        return self.__class__(
            self.antecedent.copy(),
            self.consequent.copy(),
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
        return (
            "  " * _indent
            + "if\n"
            + self.antecedent.as_text(_indent=_indent + 1)
            + "  " * _indent
            + "then\n"
            + self.consequent.as_text(_indent=_indent + 1)
        )

    def describe(self, *, _indent=0) -> str:
        """
        Return a description of the proposition.
        """
        if self.description:
            return "  " * _indent + self.description + "\n"
        return (
            "  " * _indent
            + "if\n"
            + self.antecedent.describe(_indent=_indent + 1)
            + "  " * _indent
            + "then\n"
            + self.consequent.describe(_indent=_indent + 1)
        )

    def replace(
        self,
        current_val: Term,
        new_val: Term,
        positions: list[list[int]] | None = None,
    ) -> "Implies":
        if positions is not None:
            ante_positions = [p[1:] for p in positions if p[0] == 0]
            cons_positions = [p[1:] for p in positions if p[0] == 1]
            ante_positions = None if [] in ante_positions else ante_positions
            cons_positions = None if [] in cons_positions else cons_positions
        else:
            ante_positions = None
            cons_positions = None
        new_p = self.__class__(
            self.antecedent.replace(current_val, new_val, ante_positions),
            self.consequent.replace(current_val, new_val, cons_positions),
            _is_proven=False,
        )
        return new_p

    def hypothetical_syllogism(
        self, other: Implies[UProposition, VProposition]
    ) -> Implies[TProposition, VProposition]:
        """
        Logical tactic.
        """
        assert self.is_proven, f"{self} is not proven"
        assert isinstance(other, Implies), f"{other} is not an implication"
        assert other.is_proven, f"{other} is not proven"
        assert (
            self.consequent == other.antecedent
        ), f"Does not follow logically: {self},  {other}"
        i = Implies(
            self.antecedent,
            other.consequent,
            _is_proven=True,
            _assumptions=get_assumptions(self).union(get_assumptions(other)),
            _inference=Inference(self, other, rule="hypothetical_syllogism"),
        )
        return i

    def impl_elim(self) -> Or:
        r"""Logical tactic. Given self (`A -> B`) is proven, return the corresponding
        disjunction form (`~A \/ B`)
        """
        assert self.is_proven, f"{self} is not proven"
        from pylogic.proposition.or_ import Or

        return Or(
            neg(self.antecedent),
            self.consequent,
            _is_proven=True,
            _assumptions=get_assumptions(self),
            _inference=Inference(self, rule="impl_elim"),
        )

    def definite_clause_resolve(
        self, in_body: list[Proposition] | And[Proposition, ...]
    ) -> Self | Implies[Proposition, UProposition] | UProposition:
        r"""
        Logical tactic. Given self `(A /\ B /\ C...) -> D` is proven, and
        given a conjunction (or list representing a conjunction) of some props
        in the antecedent (say A and B) is proven, return a proof of the new
        definite clause `(C /\ ...) -> D` or `C -> D` if only C is left in
        the body, or D if the antecedent is left empty.
        """
        assert self.is_proven, f"{self} is not proven"
        from pylogic.proposition.and_ import And

        in_body_is_and = isinstance(in_body, And)
        props = set(in_body.propositions if in_body_is_and else in_body)

        if in_body_is_and:
            assert in_body.is_proven, f"{in_body} is not proven"
            in_body_assumptions = get_assumptions(in_body)
        else:
            assert isinstance(in_body, list), f"{in_body} is not a list"
            in_body_assumptions: set[Proposition] = set()
            for prop in props:
                assert prop.is_proven, f"{prop} is not proven"
                in_body_assumptions = in_body_assumptions.union(get_assumptions(prop))

        assert isinstance(
            self.antecedent, And
        ), f"The antecedent of {self} is not a conjunction"
        rem_props = [
            prop.copy() for prop in self.antecedent.propositions if prop not in props
        ]
        if len(rem_props) == 1:
            return Implies(
                rem_props[0],
                self.consequent,
                _is_proven=True,
                _assumptions=get_assumptions(self).union(in_body_assumptions),
                _inference=Inference(self, in_body, rule="definite_clause_resolve"),
            )
        if len(rem_props) == 0:
            new_p = self.consequent.copy()
            new_p._is_proven = True
            new_p.deduced_from = Inference(
                self, in_body, rule="definite_clause_resolve"
            )
            new_p.from_assumptions = get_assumptions(self).union(in_body_assumptions)
            return new_p
        new_p = Implies(
            And(*rem_props),  # type: ignore
            self.consequent,
            _is_proven=True,
            _assumptions=get_assumptions(self).union(in_body_assumptions),
            _inference=Inference(self, in_body, rule="definite_clause_resolve"),
        )
        return new_p  # type:ignore

    def unit_definite_clause_resolve(
        self, in_body: Proposition
    ) -> Self | Implies[Proposition, UProposition] | UProposition:
        r"""
        Logical tactic. Given self `(A /\ B /\ C...) -> D` is proven, and
        given one of the props (say B) in the antecedent is proven,
        return a proof of the new definite clause `(A /\ C /\ ...) -> D`
        or `A -> D` if only A is left in the body, or D if the antecedent is
        left empty.
        """
        return self.definite_clause_resolve([in_body])

    def unify(self, other: Self) -> Unification | Literal[True] | None:
        if not isinstance(other, Implies):
            raise TypeError(
                f"{other} is not an instance of {self.__class__}\n\
Occured when trying to unify `{self}` and `{other}`"
            )
        d: Unification = {}
        res1 = self.antecedent.unify(other.antecedent)
        if res1 is None:
            return None
        if isinstance(res1, dict):
            for k in res1:
                if k in d and d[k] != res1[k]:
                    return None
                d[k] = res1[k]
        res2 = self.consequent.unify(other.consequent)
        if res2 is None:
            return None
        if isinstance(res2, dict):
            for k in res2:
                if k in d and d[k] != res2[k]:
                    return None
                d[k] = res2[k]
        if len(d) == 0:
            return True
        else:
            return d
