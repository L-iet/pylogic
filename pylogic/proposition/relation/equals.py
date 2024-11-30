from __future__ import annotations

from typing import TYPE_CHECKING, Callable, Self, TypeVar

from sympy import Basic, Integer

from pylogic import PythonNumeric, Term
from pylogic.expressions.abs import Abs
from pylogic.expressions.expr import Expr
from pylogic.helpers import Side
from pylogic.inference import Inference
from pylogic.proposition.proposition import Proposition, get_assumptions
from pylogic.proposition.relation.binaryrelation import BinaryRelation

if TYPE_CHECKING:
    from sympy.core.relational import Equality

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

    def __add__(self, other: Term | PythonNumeric | Equals) -> Equals:
        if isinstance(other, Equals):
            both_proven = self.is_proven and other.is_proven
            return Equals(
                self.left + other.left,
                self.right + other.right,
                _is_proven=both_proven,
                _assumptions=(
                    get_assumptions(self).union(get_assumptions(other))
                    if both_proven
                    else set()
                ),
                _inference=(
                    Inference(self, other, rule="__add__") if both_proven else None
                ),
            )
        else:
            return Equals(
                self.left + other,
                self.right + other,
                _is_proven=self.is_proven,
                _assumptions=get_assumptions(self) if self.is_proven else set(),
                _inference=Inference(self, rule="__add__") if self.is_proven else None,
            )

    def __sub__(self, other: Term | PythonNumeric | Equals) -> Equals:
        return self.__add__(-other)

    def __mul__(self, other: Term | PythonNumeric | Equals) -> Equals:
        if isinstance(other, Equals):
            both_proven = self.is_proven and other.is_proven
            return Equals(
                self.left * other.left,
                self.right * other.right,
                _is_proven=both_proven,
                _assumptions=(
                    get_assumptions(self).union(get_assumptions(other))
                    if both_proven
                    else set()
                ),
                _inference=(
                    Inference(self, other, rule="__mul__") if both_proven else None
                ),
            )
        else:
            return Equals(
                self.left * other,
                self.right * other,
                _is_proven=self.is_proven,
                _assumptions=get_assumptions(self) if self.is_proven else set(),
                _inference=Inference(self, rule="__mul__") if self.is_proven else None,
            )

    def __truediv__(self, other: Term | PythonNumeric | Equals) -> Equals:
        if isinstance(other, Equals):
            both_proven = self.is_proven and other.is_proven
            return Equals(
                self.left / other.left,
                self.right / other.right,
                _is_proven=both_proven,
                _assumptions=(
                    get_assumptions(self).union(get_assumptions(other))
                    if both_proven
                    else set()
                ),
                _inference=(
                    Inference(self, other, rule="__truediv__") if both_proven else None
                ),
            )
        else:
            return Equals(
                self.left / other,
                self.right / other,
                _is_proven=self.is_proven,
                _assumptions=get_assumptions(self) if self.is_proven else set(),
                _inference=(
                    Inference(self, rule="__truediv__") if self.is_proven else None
                ),
            )

    def __neg__(self) -> Equals:
        return Equals(
            -self.left,
            -self.right,
            _is_proven=self.is_proven,
            _assumptions=get_assumptions(self) if self.is_proven else set(),
            _inference=Inference(self, rule="__neg__") if self.is_proven else None,
        )

    def __pow__(self, other: Term | PythonNumeric | Equals) -> Equals:
        if isinstance(other, Equals):
            both_proven = self.is_proven and other.is_proven
            return Equals(
                self.left**other.left,
                self.right**other.right,
                _is_proven=both_proven,
                _assumptions=(
                    get_assumptions(self).union(get_assumptions(other))
                    if both_proven
                    else set()
                ),
                _inference=(
                    Inference(self, other, rule="__pow__") if both_proven else None
                ),
            )
        else:
            return Equals(
                self.left**other,
                self.right**other,
                _is_proven=self.is_proven,
                _assumptions=get_assumptions(self) if self.is_proven else set(),
                _inference=Inference(self, rule="__pow__") if self.is_proven else None,
            )

    def __radd__(self, other: Term | PythonNumeric) -> Equals:
        eq = Equals.reflexive(other)
        return eq.__add__(other)

    def __rsub__(self, other: Term | PythonNumeric) -> Equals:
        eq = Equals.reflexive(other)
        return eq.__sub__(other)

    def __rmul__(self, other: Term | PythonNumeric) -> Equals:
        eq = Equals.reflexive(other)
        return eq.__mul__(other)

    def __rtruediv__(self, other: Term | PythonNumeric) -> Equals:
        eq = Equals.reflexive(other)
        return eq.__truediv__(other)

    def __rpow__(self, other: Term | PythonNumeric) -> Equals:
        eq = Equals.reflexive(other)
        return eq.__pow__(other)

    def __abs__(self) -> Equals:
        return Equals(
            abs(self.left),
            abs(self.right),
            _is_proven=self.is_proven,
            _assumptions=get_assumptions(self) if self.is_proven else set(),
            _inference=Inference(self, rule="__abs__") if self.is_proven else None,
        )

    def get(self, side: Side | str) -> Term:
        if side in ["left", Side.LEFT]:
            return self.left
        elif side in ["right", Side.RIGHT]:
            return self.right
        else:
            raise ValueError(f"Invalid side: {side}")

    def _set_is_inferred(self, value: bool) -> None:
        super()._set_is_inferred(value)
        from pylogic.constant import Constant

        if self.right == Constant(0):
            self.left.is_zero = True if value else None

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
            if self.get(_checking_side) == self.get(other_side):  # type: ignore
                proven = True
            elif _doit_results[_checking_side] == _doit_results[other_side]:
                proven = True

        return proven

    def by_simplification(self) -> Self:
        """Logical inference rule."""

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

    def by_inspection_check(self) -> bool | None:
        """
        Check if self is provable by inspection.
        Returns True if self is provable by inspection, False if
        its negation is provable by inspection, and None if neither is provable.
        """
        return True if self.left == self.right else None

    def evaluate(self) -> Equals:
        """
        Evaluate the equality.
        """
        return Equals(
            self.left.evaluate(),
            self.right.evaluate(),
            _is_proven=self.is_proven,
            _assumptions=get_assumptions(self) if self.is_proven else set(),
            _inference=Inference(self, rule="evaluate") if self.is_proven else None,
        )

    def substitute_into(
        self, side: Side | str, other_prop: TProposition, **kwargs
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
            {self.get(other_side): self.get(side)}
        )
        new_prop._set_is_proven(kwargs.get("_is_proven", False))
        new_prop.from_assumptions = kwargs.get("_assumptions", set())
        new_prop.deduced_from = kwargs.get("_inference", None)
        return new_prop

    def p_substitute_into(
        self, side: Side | str, other_prop: TProposition
    ) -> TProposition:
        """
        Logical inference rule.
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
        Logical inference rule. If self is of the form Abs(x) = 0,
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

    def to_sympy(self) -> Equality:
        from sympy import Eq

        return Eq(self.left.to_sympy(), self.right.to_sympy())
