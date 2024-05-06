from __future__ import annotations
from pylogic.proposition.relation.binaryrelation import BinaryRelation
from pylogic.inference import Inference
from pylogic.proposition.proposition import Proposition, get_assumptions
from typing import TYPE_CHECKING, Literal, TypeVar, Self, Callable
from sympy import Basic, Abs, Integer

if TYPE_CHECKING:
    from pylogic.structures.sets import Set
    from pylogic.symbol import Symbol

    Term = Symbol | Set | Basic | int | float
TProposition = TypeVar("TProposition", bound="Proposition")

Side = Literal["left", "right"]


class Equals(BinaryRelation):
    is_transitive = True
    name = "Equals"
    infix_symbol = "="
    infix_symbol_latex = "="

    def __init__(
        self,
        left: Term,
        right: Term,
        is_assumption: bool = False,
        description: str = "",
        **kwargs,
    ) -> None:
        super().__init__(
            left,
            right,
            is_assumption=is_assumption,
            description=description,
            **kwargs,
        )
        self.left: Term = left
        self.right: Term = right
        self.left_doit = self.left.doit() if isinstance(self.left, Basic) else self.left
        self.right_doit = (
            self.right.doit() if isinstance(self.right, Basic) else self.right
        )
        self.doit_results: dict[Side, Term] = {
            "left": self.left_doit,
            "right": self.right_doit,
        }

    def get(self, side: Side) -> Term:
        if side == "left":
            return self.left
        else:
            return self.right

    def _check_provable_by_simplification(self, _checking_side: Side) -> bool:
        """
        To check if we can use sympy methods to simplify and prove this equality.
        Parameters
        ----------
        _checking_side: str
            "left" or "right"
        tried_doit: bool
            Whether we have tried using doit() on the arguments.
        """
        other_side: Side = "right" if _checking_side == "left" else "left"
        proven = False
        if self.left == self.right:
            proven = True
        elif isinstance(self.get(_checking_side), Basic):
            try:
                if self.get(_checking_side).equals(self.get(other_side)):  # type: ignore
                    proven = True
            except ValueError:  # TODO: Basic.equals sometimes raises ValueError
                if self.doit_results[_checking_side] == self.doit_results[other_side]:
                    proven = True

        if not proven and not (
            isinstance(self.get(_checking_side), int)
            or isinstance(self.get(_checking_side), float)
        ):
            if self.doit_results[_checking_side].dummy_eq(
                self.doit_results[other_side]
            ):  # TODO: understand more about sympy dummy_eq
                proven = True
        return proven

    def by_simplification(self) -> Self:
        """Logical tactic."""

        proven = self._check_provable_by_simplification("left")
        if not proven:
            proven = self._check_provable_by_simplification("right")
        if proven:
            new_p = self.copy()
            new_p._is_proven = True
            new_p.from_assumptions = set()
            new_p.deduced_from = Inference(self, rule="by_simplification")
            return new_p
        else:
            raise ValueError(f"{self} cannot be proven by simplification")

    def substitute_into(self, side: Side, other_prop: TProposition) -> TProposition:
        """
        If side == "left", will look for self.right in other_prop and replace it with self.left.
        Parameters
        ----------
        side: str
            "left" or "right"
        other_prop: Proposition
            Proposition to search for the other side in.
        """
        if side not in ["left", "right"]:
            raise ValueError(f"Invalid side: {side}")
        other_side: Side = "right" if side == "left" else "left"
        new_prop: TProposition = other_prop.replace(
            self.get(other_side), self.get(side)
        )
        new_prop._is_proven = False
        new_prop.from_assumptions = set()
        new_prop.deduced_from = None
        return new_prop

    def p_substitute_into(self, side: Side, other_prop: TProposition) -> TProposition:
        """
        Logical tactic.
        If side == "left", will look for self.right in other_prop and replace it with self.left.
        Returns a proven proposition.
        Parameters
        ----------
        side: str
            "left" or "right"
        other_prop: Proposition
            Proposition to search for the other side in.
        """
        assert self.is_proven, f"{self} is not proven"
        assert other_prop.is_proven, f"{other_prop} is not proven"
        new_prop: TProposition = self.substitute_into(side, other_prop)
        new_prop._is_proven = True
        new_prop.from_assumptions = get_assumptions(self).union(
            get_assumptions(other_prop)
        )
        new_prop.deduced_from = Inference(self, other_prop, rule="p_substitute_into")
        return new_prop

    def zero_abs_is_0(self) -> Equals:
        """
        Logical tactic. If self is of the form Abs(x) = 0,
        return a proof of x = 0.
        """
        assert self.is_proven, f"{self} is not proven"
        assert isinstance(self.left, Abs)
        assert self.right == Integer(0)
        return Equals(
            self.left.args[0],
            0,
            _is_proven=True,
            _assumptions=get_assumptions(self),
            _inference=Inference(self, rule="zero_abs_is_0"),
        )

    def apply(self, f: Callable[[Term], Term]) -> Equals:
        """
        Apply a function to both sides of the equality.
        """
        return Equals(
            f(self.left),
            f(self.right),
            _is_proven=self._is_proven,
            _assumptions=get_assumptions(self),
            _inference=Inference(self, rule="apply"),
        )
