from __future__ import annotations

from typing import TYPE_CHECKING, Any, Callable, Self, TypeVar

from sympy import Basic, Integer

from pylogic.expressions.abs import Abs
from pylogic.expressions.expr import Expr
from pylogic.helpers import Side
from pylogic.inference import Inference
from pylogic.proposition.proposition import Proposition, get_assumptions
from pylogic.proposition.relation.binaryrelation import BinaryRelation

if TYPE_CHECKING:
    from fractions import Fraction

    from pylogic.structures.set_ import Set
    from pylogic.symbol import Symbol

    Numeric = Fraction | int | float
    PBasic = Symbol | Numeric
    Unevaluated = Symbol | Set | Expr
    Term = Unevaluated | Numeric
else:
    Term = Any
T = TypeVar("T", bound=Term)
U = TypeVar("U", bound=Term)
TProposition = TypeVar("TProposition", bound="Proposition")


class Equals(BinaryRelation[T, U]):
    is_transitive = True
    is_reflexive = True
    is_symmetric = True
    name = "Equals"
    infix_symbol = "="
    infix_symbol_latex = "="

    def __init__(
        self,
        left: T,
        right: U,
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
        self.left: T = left
        self.right: U = right

    def get(self, side: Side | str) -> Term:
        if side in ["left", Side.LEFT]:
            return self.left
        elif side in ["right", Side.RIGHT]:
            return self.right
        else:
            raise ValueError(f"Invalid side: {side}")

    def _check_provable_by_simplification(
        self, _checking_side: Side, _doit_results: dict[Side, Term]
    ) -> bool:
        """
        To check if we can use sympy methods to simplify and prove this equality.
        Parameters
        ----------
        _checking_side: str
            "left" or "right"
        tried_doit: bool
            Whether we have tried using doit() on the arguments.
        """
        other_side: Side = Side.RIGHT if _checking_side == Side.LEFT else Side.LEFT
        proven = False
        if self.left == self.right:
            proven = True
        elif isinstance(self.get(_checking_side), (Basic, Expr)):
            try:
                if self.get(_checking_side).equals(self.get(other_side)):  # type: ignore
                    proven = True
                elif self.get(_checking_side) == self.get(other_side):  # type: ignore
                    proven = True
            except ValueError:  # TODO: Basic.equals sometimes raises ValueError
                if _doit_results[_checking_side] == _doit_results[other_side]:
                    proven = True

        return proven

    def by_simplification(self) -> Self:
        """Logical tactic."""

        left_doit = (
            self.left.evaluate() if isinstance(self.left, (Basic, Expr)) else self.left
        )
        right_doit = (
            self.right.evaluate()
            if isinstance(self.right, (Basic, Expr))
            else self.right
        )
        doit_results: dict[Side, Term] = {
            Side.LEFT: left_doit,
            Side.RIGHT: right_doit,
        }

        proven = self._check_provable_by_simplification(Side.LEFT, doit_results)
        if not proven:
            proven = self._check_provable_by_simplification(Side.RIGHT, doit_results)
        if proven:
            new_p = self.copy()
            new_p._set_is_proven(True)
            new_p.from_assumptions = set()
            new_p.deduced_from = Inference(self, rule="by_simplification")
            return new_p
        else:
            raise ValueError(f"{self} cannot be proven by simplification")

    def substitute_into(
        self, side: Side | str, other_prop: TProposition
    ) -> TProposition:
        """
        If side == Side.LEFT, will look for self.right in other_prop and replace it with self.left.
        Parameters
        ----------
        side: Side
            Side to appear in the result.
        other_prop: Proposition
            Proposition to search for the other side in.
        """
        if side not in (Side.LEFT, Side.RIGHT, "left", "right"):
            raise ValueError(f"Invalid side: {side}")
        if side == "left":
            side = Side.LEFT
        elif side == "right":
            side = Side.RIGHT
        other_side: Side = Side.RIGHT if side == Side.LEFT else Side.LEFT
        new_prop: TProposition = other_prop.replace(
            self.get(other_side), self.get(side)
        )
        new_prop._set_is_proven(False)
        new_prop.from_assumptions = set()
        new_prop.deduced_from = None
        return new_prop

    def p_substitute_into(
        self, side: Side | str, other_prop: TProposition
    ) -> TProposition:
        """
        Logical tactic.
        If side == Side.LEFT, will look for self.right in other_prop and replace it with self.left.
        Returns a proven proposition.
        Parameters
        ----------
        side: Side
            Side to appear in the result.
        other_prop: Proposition
            Proposition to search for the other side in.
        """
        assert self.is_proven, f"{self} is not proven"
        assert other_prop.is_proven, f"{other_prop} is not proven"
        new_prop: TProposition = self.substitute_into(side, other_prop)
        new_prop._set_is_proven(True)
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
            self.left.args[0],  # type: ignore
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
            _is_proven=self.is_proven,
            _assumptions=get_assumptions(self),
            _inference=Inference(self, rule="apply"),
        )

    def symmetric(self) -> Equals[U, T]:
        return super().symmetric()  # type: ignore
