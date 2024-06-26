from __future__ import annotations
from typing import TYPE_CHECKING, Self, TypeVar, Generic, Literal
from abc import ABC, abstractmethod

from pylogic.proposition.proposition import Proposition
from pylogic.variable import Variable

from sympy import Basic, latex

if TYPE_CHECKING:
    from pylogic.structures.sets import Set
    from pylogic.symbol import Symbol

    Term = Symbol | Set | Basic | int | float
    Unification = dict[Variable, Term]

TProposition = TypeVar("TProposition", bound="Proposition")


class _Quantified(Proposition, Generic[TProposition], ABC):
    def __init__(
        self,
        _q: str,
        variable: Variable,
        inner_proposition: TProposition,
        is_assumption: bool = False,
        description: str = "",
        **kwargs,
    ) -> None:
        if not isinstance(variable, Variable):
            raise TypeError(f"{variable} is not a variable")
        if variable in inner_proposition.bound_vars:
            raise ValueError(
                f"Variable {variable} is already bound in {inner_proposition}"
            )
        super().__init__(
            f"{_q} {variable}: {inner_proposition.name}",
            is_assumption,
            args=[],
            description=description,
            **kwargs,
        )
        self.inner_proposition: TProposition = inner_proposition
        self.variable: Variable = variable
        self.variable.is_bound = True
        self._q = _q
        self.is_atomic = False
        self.bound_vars = inner_proposition.bound_vars.union({variable})

    def __repr__(self) -> str:
        return f"{self._q} {self.variable}: {self.inner_proposition}"

    def __hash__(self) -> int:
        return hash((self._q, self.variable, self.inner_proposition))

    def as_text(self, *, _indent=0) -> str:
        """
        Return a text representation of the proposition.
        """
        return (
            "  " * _indent
            + f"{self._q} {self.variable}:\n"
            + self.inner_proposition.as_text(_indent=_indent + 1)
        )

    def describe(self, *, _indent=0) -> str:
        """
        Return a text representation of the proposition.
        """
        if self.description:
            return "  " * _indent + self.description + "\n"
        return (
            "  " * _indent
            + f"{self._q} {self.variable}:\n"
            + self.inner_proposition.describe(_indent=_indent + 1)
        )

    def copy(self) -> Self:
        assert self.__class__ != _Quantified
        return self.__class__(
            self.variable,  # type: ignore
            self.inner_proposition.copy(),  # type: ignore
            is_assumption=self.is_assumption,  # type: ignore
            description=self.description,
            _is_proven=self._is_proven,
            _assumptions=self.from_assumptions,
            _inference=self.deduced_from,
        )

    def replace(
        self,
        current_val: Term,
        new_val: Term,
        positions: list[list[int]] | None = None,
    ) -> Self:
        # assert not isinstance(new_val, Var), f"{new_val} is a Var"
        new_p: Self = self.copy()
        new_p.inner_proposition = new_p.inner_proposition.replace(
            current_val, new_val, positions
        )
        new_p._is_proven = False
        new_p.from_assumptions = set()
        new_p.deduced_from = None
        return new_p

    def _latex(self, printer=None) -> str:
        q_arg = self.variable
        arg_latex = q_arg._latex() if hasattr(q_arg, "_latex") else latex(q_arg)  # type: ignore
        return rf"\{self._q} {arg_latex}: {self.inner_proposition._latex()}"

    def unify(self, other: Self) -> Unification | Literal[True] | None:
        if self.__class__ != other.__class__:
            raise TypeError(
                f"{other} is not an instance of {self.__class__}\n\
Occured when trying to unify `{self}` and `{other}`"
            )
        return self.inner_proposition.unify(other.inner_proposition)
