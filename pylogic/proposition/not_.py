from __future__ import annotations

from typing import TYPE_CHECKING, Generic, Literal, Self, TypedDict, TypeVar, overload

from pylogic.proposition.proposition import Proposition, get_assumptions

if TYPE_CHECKING:
    from fractions import Fraction


    from pylogic.expressions.expr import Expr
    from pylogic.proposition.implies import Implies
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


@overload
def neg(
    p: Not[TProposition], is_assumption: bool = False, **kwargs
) -> TProposition: ...


@overload
def neg(
    p: TProposition, is_assumption: bool = False, **kwargs
) -> Not[TProposition]: ...


def neg(
    p: Not[TProposition] | TProposition, is_assumption: bool = False, **kwargs
) -> Not[TProposition] | TProposition:
    """
    Given a proposition, return its negation.
    """
    if isinstance(p, Not):
        return p.negated
    return Not(p, is_assumption, **kwargs)


def are_negs(p: Proposition, q: Proposition) -> bool:
    """Given two propositions, determine if they are negations
    of each other.
    """
    if isinstance(p, Not):
        return p.negated == q
    elif isinstance(q, Not):
        return q.negated == p
    return False


class Not(Proposition, Generic[TProposition]):
    tactics: list[Tactic] = [
        {"name": "modus_tollens", "arguments": ["Implies"]},
        {"name": "de_morgan", "arguments": []},
    ]

    def __init__(
        self,
        negated: TProposition,
        is_assumption: bool = False,
        description: str = "",
        **kwargs,
    ) -> None:
        self.negated: TProposition = negated
        name = rf"~{negated}"
        super().__init__(name, is_assumption, description=description, **kwargs)
        self.is_atomic = False
        self.bound_vars = negated.bound_vars.copy()

    def __eq__(self, other: Proposition) -> bool:
        if isinstance(other, Not):
            return other.negated == self.negated
        return False

    def __hash__(self) -> int:
        return hash(("not", self.negated))

    def copy(self) -> Self:
        return self.__class__(
            self.negated.copy(),
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
            + "it is false that\n"
            + self.negated.as_text(_indent=_indent + 1)
        )

    def describe(self, *, _indent=0) -> str:
        """
        Return a description of the proposition.
        """
        if self.description:
            return "  " * _indent + self.description + "\n"
        return (
            "  " * _indent
            + "it is false that\n"
            + self.negated.describe(_indent=_indent + 1)
        )

    def replace(
        self,
        current_val: Term,
        new_val: Term,
        positions: list[list[int]] | None = None,
    ) -> Self:
        new_p = self.__class__(
            self.negated.replace(current_val, new_val, positions=positions)
        )
        return new_p

    @overload
    def modus_tollens(
        self,
        other: Implies[Not[UProposition], TProposition],
    ) -> UProposition: ...

    @overload
    def modus_tollens(
        self,
        other: Implies[UProposition, TProposition],
    ) -> Not[UProposition]: ...

    def modus_tollens(
        self,
        other: (
            Implies[Not[UProposition], TProposition]
            | Implies[UProposition, TProposition]
        ),
    ) -> UProposition | Not[UProposition]:
        """
        Logical tactic.
        other: Implies
            Must be an implication that has been proven whose structure is
            OtherProposition -> ~self
        """
        return super().modus_tollens(other)  # type: ignore

    def _latex(self, printer=None) -> str:
        return rf"\neg{{{self.negated._latex()}}}"

    def de_morgan(self) -> Proposition:
        """
        Apply De Morgan's law to this negation.
        """
        from pylogic.inference import Inference
        from pylogic.proposition.and_ import And
        from pylogic.proposition.or_ import Or

        if isinstance(self.negated, And):
            negs: list[Proposition] = [
                neg(p.de_morgan()) for p in self.negated.propositions  # type:ignore
            ]
            return Or(
                *negs,  # type: ignore
                _is_proven=self.is_proven,
                _assumptions=get_assumptions(self).copy(),
                _inference=Inference(self, rule="de_morgan"),
            )
        elif isinstance(self.negated, Or):
            negs: list[Proposition] = [
                neg(p.de_morgan()) for p in self.negated.propositions  # type:ignore
            ]
            return And(
                *negs,  # type: ignore
                _is_proven=self.is_proven,
                _assumptions=get_assumptions(self).copy(),
                _inference=Inference(self, rule="de_morgan"),
            )
        elif self.negated.is_atomic:
            return self.copy()

        return neg(
            self.negated.de_morgan(),
            _is_proven=self.is_proven,
            _assumptions=get_assumptions(self).copy(),
            _inference=Inference(self, rule="de_morgan"),
        )

    def unify(self, other: Self) -> Unification | Literal[True] | None:
        if not isinstance(other, Not):
            raise TypeError(
                f"{other} is not an instance of {self.__class__}\n\
Occured when trying to unify `{self}` and `{other}`"
            )
        return self.negated.unify(other.negated)
