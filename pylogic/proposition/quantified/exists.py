from __future__ import annotations
from pylogic.proposition.proposition import Proposition
from pylogic.proposition.quantified.quantified import _Quantified
from pylogic.variable import Variable
from typing import TYPE_CHECKING, TypedDict, TypeVar, Self

if TYPE_CHECKING:
    from sympy import Basic
    from pylogic.proposition.quantified.forall import Forall
    from pylogic.proposition.implies import Implies

    SympyExpression = Basic | int | float
from pylogic.set.sets import Set
import sympy as sp
import pylogic.p_symbol as ps

TProposition = TypeVar("TProposition", bound="Proposition")
UProposition = TypeVar("UProposition", bound="Proposition")
B = TypeVar("B", bound="Proposition")
Tactic = TypedDict("Tactic", {"name": str, "arguments": list[str]})


class Exists(_Quantified[TProposition]):
    tactics: list[Tactic] = [{"name": "exists_modus_ponens", "arguments": ["Forall"]}]

    @classmethod
    def from_proposition(
        cls,
        existential_var_name: str,
        expression_to_replace: Set | SympyExpression | None,
        inner_proposition: TProposition,
        positions: list[list[int]] | None = None,
        is_assumption: bool = False,
        is_real: bool = True,
        _is_proven: bool = False,
    ) -> Exists[TProposition]:
        r"""
        positions: list[list[int]]
            This is a list containing the positions of the expression_to_replace in self.
            If None, we will search for all occurences of the expression_to_replace in self.
            This is a nested list representing the path we need to go down in the proposition tree,
            For example, if self is
            (forall x: (p1 x -> p2 x) /\ (p3 x) /\ (p4 x)) -> (p5 x)
            existential_var = q
            and positions = [[0, 0, 0], [0, 2], [1]]
            we end up with
            exists q: (forall x: (p1 q -> p2 x) /\ (p3 x) /\ (p4 q)) -> (p5 q)
        """
        variable = Variable(existential_var_name, real=is_real)
        if expression_to_replace is not None:
            inner_proposition = inner_proposition.replace(
                expression_to_replace, variable, positions=positions
            )
        return cls(
            variable,
            inner_proposition,
            is_assumption,
            _is_proven,
        )

    def __init__(
        self,
        variable: Variable,
        inner_proposition: TProposition,
        is_assumption: bool = False,
        _is_proven: bool = False,
    ) -> None:
        super().__init__(
            "exists",
            variable,
            inner_proposition,
            is_assumption,
            _is_proven,
        )

    def __eq__(self, other: Proposition) -> bool:
        if isinstance(other, Exists):
            return self.inner_proposition == other.inner_proposition
        return False

    def __iter__(self):
        return iter((self.variable, self.inner_proposition))

    def copy(self) -> Self:
        return self.__class__(
            self.variable,
            self.inner_proposition.copy(),
            self.is_assumption,
            _is_proven=self.is_proven,
        )

    def exists_modus_ponens(self, other: Forall[Implies[TProposition, B]]) -> Exists[B]:
        """
        Logical tactic. If self is exists x: P(x) and given forall x: P(x) -> Q(x)
        and each is proven, conclude exists x: Q(x).
        """
        from pylogic.proposition.quantified.forall import Forall

        assert self.is_proven, f"{self} is not proven"
        assert isinstance(other, Forall), f"{other} is not a forall statement"
        assert other.is_proven, f"{other} is not proven"
        assert self.inner_proposition == other.inner_proposition.antecedent

        other_cons = other.inner_proposition.consequent.copy()
        new_p = Exists(
            variable=other.variable,
            inner_proposition=other_cons,  # type: ignore
            is_assumption=False,
            _is_proven=True,
        )
        return new_p
