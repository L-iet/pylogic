# pyright: reportInvalidTypeForm=false
from __future__ import annotations

from typing import TYPE_CHECKING, Generic, Literal, Self, TypedDict, TypeVar

from pylogic.helpers import find_first
from pylogic.inference import Inference
from pylogic.proposition.implies import Implies
from pylogic.proposition.not_ import neg
from pylogic.proposition.proposition import Proposition, get_assumptions

if TYPE_CHECKING:
    from fractions import Fraction

    from pylogic.expressions.expr import Expr
    from pylogic.proposition.and_ import And
    from pylogic.proposition.not_ import Not
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


class Iff(Proposition, Generic[TProposition, UProposition]):
    tactics: list[Tactic] = [
        {"name": "forward_implication", "arguments": []},
        {"name": "reverse_implication", "arguments": []},
        {"name": "converse", "arguments": []},
        {"name": "inverse", "arguments": []},
        {"name": "contrapositive", "arguments": []},
        {"name": "to_conjunction", "arguments": []},
    ]

    def __init__(
        self,
        left: TProposition,
        right: UProposition,
        is_assumption: bool = False,
        description: str = "",
        **kwargs,
    ) -> None:
        self.left = left
        self.right = right
        name = f"{left.name} <-> {right.name}"
        super().__init__(name, is_assumption, description=description, **kwargs)
        self.is_atomic = False
        self.bound_vars = left.bound_vars.union(right.bound_vars)

    def __eq__(self, other: Proposition) -> bool:
        if isinstance(other, Iff):
            return self.left == other.left and self.right == other.right
        return False

    def __hash__(self) -> int:
        return hash(("iff", self.left, self.right))

    def __repr__(self) -> str:
        return f"[{self.left} <-> {self.right}]"

    def _latex(self, printer=None) -> str:
        return (
            rf"\left({self.left._latex()} \leftrightarrow {self.right._latex()}\right)"
        )

    def copy(self) -> Self:
        return self.__class__(
            self.left,
            self.right,
            is_assumption=self.is_assumption,
            description=self.description,
            _is_proven=self._is_proven,
            _assumptions=self.from_assumptions,
            _inference=self.deduced_from,
        )

    def deepcopy(self) -> Self:
        return self.__class__(
            self.left.deepcopy(),
            self.right.deepcopy(),
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
            self.left.as_text(_indent=_indent + 1)
            + "  " * _indent
            + "if and only if\n"
            + self.right.as_text(_indent=_indent + 1)
        )

    def describe(self, *, _indent=0) -> str:
        """
        Return a description of the proposition.
        """
        if self.description:
            return "  " * _indent + self.description + "\n"
        return (
            self.left.describe(_indent=_indent + 1)
            + "  " * _indent
            + "if and only if\n"
            + self.right.describe(_indent=_indent + 1)
        )

    def replace(
        self,
        current_val: Term,
        new_val: Term,
        positions: list[list[int]] | None = None,
    ) -> Self:
        if positions is not None:
            ante_positions = [p[1:] for p in positions if p[0] == 0]
            cons_positions = [p[1:] for p in positions if p[0] == 1]
            ante_positions = None if [] in ante_positions else ante_positions
            cons_positions = None if [] in cons_positions else cons_positions
        else:
            ante_positions = None
            cons_positions = None
        new_p = self.__class__(
            self.left.replace(current_val, new_val, ante_positions),
            self.right.replace(current_val, new_val, cons_positions),
            _is_proven=False,
        )
        return new_p

    def forward_implication(self) -> Implies[TProposition, UProposition]:
        r"""Logical tactic. Given self (`A <-> B`) is proven, return the forward
        implication `A -> B`.
        """
        return Implies(
            self.left,
            self.right,
            _is_proven=self.is_proven,
            _assumptions=get_assumptions(self),
            _inference=Inference(self, rule="forward_implication"),
        )

    def reverse_implication(self) -> Implies[UProposition, TProposition]:
        r"""Logical tactic. Given self (`A <-> B`) is proven, return the reverse
        implication `B -> A`.
        """
        return Implies(
            self.right,
            self.left,
            _is_proven=self.is_proven,
            _assumptions=get_assumptions(self),
            _inference=Inference(self, rule="reverse_implication"),
        )

    def converse(self) -> Iff[UProposition, TProposition]:
        r"""Logical tactic. Given self (`A <-> B`) is proven, return the converse
        `B <-> A`.
        """
        return Iff(
            self.right,
            self.left,
            _is_proven=self.is_proven,
            _assumptions=get_assumptions(self),
            _inference=Inference(self, rule="converse"),
        )

    def inverse(self) -> Iff[Not[TProposition], Not[UProposition]]:
        r"""Logical tactic. Given self (`A <-> B`) is proven, return the inverse
        `~A <-> ~B`.
        """
        return Iff(
            neg(self.left),
            neg(self.right),
            _is_proven=self.is_proven,
            _assumptions=get_assumptions(self),
            _inference=Inference(self, rule="inverse"),
        )

    def contrapositive(self) -> Iff[Not[UProposition], Not[TProposition]]:
        r"""Logical tactic. Given self (`A <-> B`) is proven, return the contrapositive
        `~B <-> ~A`.
        """
        return Iff(
            neg(self.right),
            neg(self.left),
            _is_proven=self.is_proven,
            _assumptions=get_assumptions(self),
            _inference=Inference(self, rule="contrapositive"),
        )

    def to_conjunction(
        self,
    ) -> And[Implies[TProposition, UProposition], Implies[UProposition, TProposition]]:
        r"""If self is of the form `A <-> B`, returns a proposition of the form `A -> B and B -> A`"""
        return And(
            self.forward_implication(),
            self.reverse_implication(),
            description=self.description,
            _is_proven=self.is_proven,
            _assumptions=get_assumptions(self),
            _inference=Inference(self, rule="to_conjunction"),
        )

    def has_as_subproposition(self, other: Proposition) -> bool:
        """
        Check if other is a subproposition of self.
        """
        if self == other:
            return True
        first_other_occurs_in = find_first(
            lambda p: p.has_as_subproposition(other), [self.left, self.right]
        )
        return first_other_occurs_in is not None
