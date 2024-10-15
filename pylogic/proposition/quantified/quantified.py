from __future__ import annotations

from abc import ABC
from typing import Callable, Generic, Literal, Self, TypeVar


from pylogic import Term, Unification
from pylogic.proposition.proposition import Proposition
from pylogic.variable import Variable

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
        self.variables = inner_proposition.variables.copy()
        self.variables.add(variable)
        self.constants = inner_proposition.constants.copy()
        self.sets = inner_proposition.sets.copy()
        self.class_ns = inner_proposition.class_ns.copy()

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
            variable=self.variable,
            inner_proposition=self.inner_proposition,
            is_assumption=self.is_assumption,
            description=self.description,
            _is_proven=self._is_proven,
            _assumptions=self.from_assumptions,
            _inference=self.deduced_from,
        )  # type: ignore

    def deepcopy(self) -> Self:
        assert self.__class__ != _Quantified
        return self.__class__(
            variable=self.variable.deepcopy(),
            inner_proposition=self.inner_proposition.deepcopy(),
            is_assumption=self.is_assumption,
            description=self.description,
            _is_proven=self._is_proven,
            _assumptions=self.from_assumptions,
            _inference=self.deduced_from,
        )  # type: ignore

    def replace(
        self,
        replace_dict: dict[Term, Term],
        positions: list[list[int]] | None = None,
        equal_check: Callable[[Term, Term], bool] | None = None,
    ) -> Self:
        new_p: Self = self.copy()
        new_p.inner_proposition = new_p.inner_proposition.replace(
            replace_dict, positions=positions, equal_check=equal_check
        )
        new_p._set_is_proven(False)
        new_p.from_assumptions = set()
        new_p.deduced_from = None
        return new_p

    def _latex(self, printer=None) -> str:
        q_arg = self.variable
        arg_latex = q_arg._latex()
        return rf"\{self._q} {arg_latex}: {self.inner_proposition._latex()}"

    def unify(self, other: Self) -> Unification | Literal[True] | None:
        if self.__class__ != other.__class__:
            raise TypeError(
                f"{other} is not an instance of {self.__class__}\n\
Occured when trying to unify `{self}` and `{other}`"
            )
        return self.inner_proposition.unify(other.inner_proposition)

    def has_as_subproposition(self, other: Proposition) -> bool:
        """
        Check if other is a subproposition of self.
        """
        if self == other:
            return True
        return self.inner_proposition.has_as_subproposition(other)
