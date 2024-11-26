from __future__ import annotations

from abc import ABC
from typing import Callable, Generic, Literal, Self, TypeVar

from pylogic import Term, Unification
from pylogic.proposition.proposition import Proposition
from pylogic.variable import Variable

TProposition = TypeVar("TProposition", bound="Proposition")


class _Quantified(Proposition, Generic[TProposition], ABC):
    """
    Note that the variable of a quantified proposition is bound and
    has no assumptions.
    """

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
        var = self._reset_variable(
            variable
        ).copy()  # make a copy in case user uses the same variable elsewhere
        self.variable: Variable = var
        self.variable.is_bound = True
        self._q = _q
        self.is_atomic = False
        self.bound_vars = inner_proposition.bound_vars.union({var})
        self.variables = inner_proposition.variables.copy()
        self.variables.add(var)
        self.constants = inner_proposition.constants.copy()
        self.sets = inner_proposition.sets.copy()
        self.class_ns = inner_proposition.class_ns.copy()

    def __str__(self) -> str:
        from pylogic.proposition.not_ import Not

        mid_part = str(self.variable)
        if self._bin_symb is not None:
            mid_part += f" {self._bin_symb} {self.set_}"

        innermost_prop = getattr(self, self._innermost_prop_attr)
        # only wrap the innermost proposition in parentheses if it is not atomic
        # and not a quantified proposition
        inner_part = (
            f"({innermost_prop})"
            if (not innermost_prop.is_atomic)
            and (not isinstance(innermost_prop, (_Quantified, Not)))
            else str(innermost_prop)
        )
        return f"{self._q} {mid_part}: {inner_part}"

    def _latex(self, printer=None) -> str:
        from pylogic.proposition.not_ import Not

        mid_part = self.variable._latex()
        bin_symb_to_latex = {"subset of": r"\subseteq", "in": r"\in"}
        quant_symb_to_latex = {
            "forall": r"\forall",
            "exists": r"\exists",
            "exists 1": r"\exists !",
        }
        if self._bin_symb is not None:
            mid_part += f" {bin_symb_to_latex[self._bin_symb]} {self.set_._latex()}"

        innermost_prop = getattr(self, self._innermost_prop_attr)
        # only wrap the innermost proposition in parentheses if it is not atomic
        # and not a quantified proposition
        inner_part = (
            rf"\left({innermost_prop._latex()}\right)"
            if (not innermost_prop.is_atomic)
            and (not isinstance(innermost_prop, (_Quantified, Not)))
            else innermost_prop._latex()
        )
        return rf"{quant_symb_to_latex[self._q]} {mid_part}: {inner_part}"

    def __repr__(self) -> str:
        if self._bin_symb is not None:
            return f"{self.__class__.__name__}({self.variable!r}, {self.set_!r}, {getattr(self, self._innermost_prop_attr)!r})"
        return f"{self.__class__.__name__}({self.variable!r}, {getattr(self, self._innermost_prop_attr)!r})"

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

    def _reset_variable(self, variable: Variable) -> Variable:
        # we don't reset is_set, is_list
        # etc because those denote the type of the variable
        # rather than properties of the variable itself
        variable._is_real = None
        variable._is_rational = None
        variable._is_integer = None
        variable._is_natural = None
        variable._is_nonnegative = None
        variable._is_nonpositive = None
        variable._is_even = None
        variable._is_zero = None
        return variable

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

    def rename_variable(self, new_name: str) -> Self:
        """
        Logical inference rule. Rename the bound variable.
        """
        from pylogic.inference import Inference

        new_var = Variable(new_name)
        new_p = self.replace({self.variable: new_var})
        if self.is_proven:
            new_p._set_is_proven(True)
            new_p.deduced_from = Inference(self, rule="rename_variable")
            new_p.from_assumptions = self.from_assumptions
        return new_p

    def replace(
        self,
        replace_dict: dict[Term, Term],
        positions: list[list[int]] | None = None,
        equal_check: Callable[[Term, Term], bool] | None = None,
    ) -> Self:
        new_var = self.variable
        if self.variable in replace_dict:
            assert isinstance(
                replace_dict[self.variable], Variable
            ), "Cannot replace variable with non-variable"
            new_var = replace_dict[self.variable]
        new_p = self.__class__(
            variable=new_var,
            inner_proposition=self.inner_proposition.replace(
                replace_dict, positions, equal_check=equal_check
            ),
        )
        return new_p

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
