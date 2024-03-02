from __future__ import annotations
from typing import Self, Protocol

import sympy as sp
from sympy.printing.latex import LatexPrinter

from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from pylogic.set.sets import Set
    from pylogic.proposition.relation.equals import Equals
    from pylogic.proposition.and_ import And
    from pylogic.proposition.implies import Implies
    from pylogic.proposition.quantified.exists import Exists
    from pylogic.proposition.quantified.forall import Forall


SympyExpression = sp.Basic | int | float

latex_printer = LatexPrinter()

#####################################################


class _Statement:
    name: str
    args: dict[str, type[Set] | type[SympyExpression]] = {}
    args_order: list[str] = []
    arg_values: dict[str, Set | SympyExpression] = {}
    is_assumption: bool
    is_proven: bool

    def show_args(self) -> None: ...


####################################################


class Proposition(_Statement):
    def __init__(
        self,
        name: str,
        is_assumption: bool = False,
        completed_args: dict[str, Set | SympyExpression] | None = None,
        completed_args_order: list[str] | None = None,
        show_arg_position_names: bool = False,
        _is_proven: bool = False,
    ) -> None:
        """
        name: str
            Name of the proposition. Typically the first part of the __repr__.
        is_assumption: bool
            Whether this proposition is an assumption.
        completed_args: dict[str, Set | SympyExpression]
            Dictionary of argument position identifiers and their values. The values are
            typically Set or SympyExpression instances.
        show_arg_position_names: bool
            Whether to show the argument position identifiers in the __repr__.
            This is useful for propositions with multiple arguments of the same type.
            In p(completed_args={x:x1, y:x2}), the argument position identifiers are x and y.
            If this is False, the __repr__ will be p x1 x2.
            If this is True, the __repr__ will be p x=x1 y=x2.
        """
        completed_args = completed_args or {}
        if len(completed_args) == 0:
            completed_args_order = []
        elif completed_args_order is None or len(completed_args_order) == 0:
            completed_args_order = sorted(list(completed_args.keys()))
        completed_args = {k: completed_args[k] for k in completed_args_order}
        name = name.strip()
        assert set(name.split("_")) != {""}, "Proposition name cannot be empty"
        self.name = name
        self.show_arg_position_names = show_arg_position_names
        self.is_assumption = is_assumption
        self.completed_args = completed_args
        self.completed_args_order = completed_args_order
        self._is_proven = _is_proven

    def __eq__(self, other: "Proposition") -> bool:
        return self.name == other.name and self.completed_args == other.completed_args

    def __repr__(self) -> str:
        s = ""
        for arg_id in self.completed_args_order:
            s += (
                f"{arg_id}={self.completed_args[arg_id]} "
                if self.show_arg_position_names
                else f"{self.completed_args[arg_id]} "
            )
        return f"{self.name} {s}".strip()

    def __copy__(self) -> "Proposition":
        return self.copy()

    def _latex(self, printer=latex_printer) -> str:
        s = ""
        for arg_id in self.completed_args_order:
            printed_arg = printer._print(self.completed_args[arg_id])
            s += (
                f"{arg_id}={printed_arg} "
                if self.show_arg_position_names
                else f"{printed_arg} "
            )
        return rf"\text{{{self.name}}} {s}"

    def _repr_latex_(self) -> str:
        return f"$${self._latex()}$$"

    @property
    def is_proven(self) -> bool:
        return self._is_proven or self.is_assumption

    def copy(self) -> "Proposition":
        return Proposition(
            self.name,
            self.is_assumption,
            completed_args=self.completed_args.copy(),
            completed_args_order=self.completed_args_order.copy(),
            show_arg_position_names=self.show_arg_position_names,
            _is_proven=self.is_proven,
        )

    def replace(
        self,
        current_val: Set | SympyExpression,
        new_val: Set | SympyExpression,
        positions: list[list[int]] | None = None,
    ) -> Self:
        r"""
        Parameters
        ----------
        positions: list[list[int]]
            This is a list containing the positions of the expression_to_replace in self.
            If None, we will replace for all occurences of the expression_to_replace in self.
            This is a nested list representing the path we need to go down in the proposition tree,
            For example, if self is
            (forall x: (p1 x -> p2 x) /\ (p3 x) /\ (p4 x)) -> (p5 x)
            current_val = x
            new_val = p
            and positions = [[0, 0, 0], [0, 2], [1]]
            we end up with
            exists q: (forall x: (p1 q -> p2 x) /\ (p3 x) /\ (p4 q)) -> (p5 q)
            The quantified variable in a forall is never replaced itself. Due to this,
            the positions array for forall goes directly into the inner proposition.
            Same for exists.
            In the example above, the first list [0,0,0] refers to the x in p1 x, not (p1 x -> p2 x).
        """
        new_p = self.copy()
        index = -1
        for arg_id in new_p.completed_args_order:
            index += 1
            if (positions is not None) and not [index] in positions:
                continue
            if new_p.completed_args[arg_id] == current_val:
                new_p.completed_args[arg_id] = new_val
            elif isinstance(new_p.completed_args[arg_id], sp.Basic):
                new_p.completed_args[arg_id] = new_p.completed_args[arg_id].subs(
                    current_val, new_val
                )
        new_p._is_proven = False
        return new_p

    def substitute(self, side: str, equality: "Equals") -> Self:
        """
        Parameters
        ----------
        side: str
            "left" or "right"
        equality: Equals
            An equality proposition. We look for the other side of the equality
            in self and replace it with the 'side'.
        """
        return equality.substitute_into(side, self)

    def p_substitute(self, side: str, equality: "Equals") -> Self:
        """
        Logical tactic.
        Parameters
        ----------
        side: str
            "left" or "right"
        equality: Equals
            An equality proposition. We look for the other side of the equality
            in self and replace it with the 'side'.
        Returns a proven proposition.
        """
        assert self.is_proven, f"{self} is not proven"
        assert equality.is_proven, f"{equality} is not proven"
        new_p = self.substitute(side, equality)
        new_p._is_proven = True
        return new_p

    def implies(
        self,
        other: "Proposition",
        is_assumption: bool = False,
    ) -> "Implies":
        from pylogic.proposition.implies import Implies

        return Implies(self, other, is_assumption)

    def and_(
        self,
        *others: "Proposition",
        is_assumption: bool = False,
    ) -> "And":
        from pylogic.proposition.and_ import And

        return And(self, *others, is_assumption=is_assumption)

    def and_reverse(
        self,
        *others: "Proposition",
        is_assumption: bool = False,
    ) -> "And":
        from pylogic.proposition.and_ import And

        return And(*others, self, is_assumption=is_assumption)

    def p_and(self, *others: "Proposition") -> "And":
        """Logical tactic.
        Same as and_, but returns a proven proposition when self and all others are proven.
        """
        assert len(others) > 0, "Must provide at least one proposition"
        assert self.is_proven, f"{self} is not proven"
        for o in others:
            assert o.is_proven, f"{o} is not proven"
        new_p = self.and_(*others)
        new_p._is_proven = True
        return new_p

    def p_and_reverse(self, *others: "Proposition") -> "And":
        """Logical tactic.
        Same as and_reverse, but returns a proven proposition when self and all others are proven.
        """
        assert len(others) > 0, "Must provide at least one proposition"
        assert self.is_proven, f"{self} is not proven"
        for o in others:
            assert o.is_proven, f"{o} is not proven"
        new_p = self.and_reverse(*others)
        new_p._is_proven = True
        return new_p

    def modus_ponens(self, other: "Implies") -> "Proposition":
        """
        Logical tactic.
        other: Implies
            Must be an implication that has been proven whose structure is
            self.name -> OtherProposition
        """
        assert self.is_proven, f"{self.name} is not proven"
        assert other.is_proven, f"{other.name} is not proven"
        assert other.antecedent == self, f"{other.name} does not imply {self.name}"
        new_p = other.consequent.copy()
        new_p._is_proven = True
        return new_p

    def is_one_of(self, other: "And", _recursive: bool = False) -> Self:
        r"""
        Logical tactic.
        If we have proven other, we can prove any of the propositions in it.
        other: And
            Must be an And that has been proven whose structure is
            self /\ OtherProposition
        """
        if not _recursive:
            assert other.is_proven, f"{other} is not proven"
        from pylogic.proposition.and_ import And

        for p in other.propositions:
            if p == self:
                new_p = self.copy()
                new_p._is_proven = True
                return new_p
            elif isinstance(p, And):
                try:
                    return self.is_one_of(p, _recursive=True)
                except ValueError:
                    continue
        raise ValueError(f"{self} is not in {other}")

    def is_special_case_of(self, other: "Forall") -> Self:
        """
        Logical tactic.
        other: Proposition
            A proven forall proposition that implies this proposition.
        """
        from pylogic.proposition.quantified.forall import Forall

        assert isinstance(other, Forall), f"{other} is not a forall statement"
        assert other.is_proven, f"{other} is not proven"
        assert (
            self.name == other.inner_proposition.name
        ), f"{self} is not a special case of {other}"
        for arg_id in self.completed_args:
            if arg_id in other.completed_args:
                assert type(self.completed_args[arg_id]) == type(
                    other.completed_args[arg_id]
                ), f"{self} is not a special case of {other}: {arg_id} is not the same type"
            else:
                raise ValueError(
                    f"{self} is not a special case of {other}: {arg_id} is not in the completed arguments of {other}"
                )
        new_p = self.copy()
        new_p._is_proven = True
        return new_p

    def followed_from(self, *assumptions: "Proposition") -> "Implies":
        """
        Logical tactic.
        Given self is proven, return a new proposition that is an implication of the form
        assumptions -> self.
        *assumptions: Proposition
            Propositions that implied this proposition.
        This function only accepts propositions that were explicitly declared as assumptions.
        """
        assert self.is_proven, f"{self} is not proven"
        assert len(assumptions) > 0, "Must provide at least one other assumption"
        for a in assumptions:
            assert a.is_assumption, f"{a} is not an assumption"
        from pylogic.proposition.and_ import And

        if len(assumptions) == 1:
            new_p = assumptions[0].implies(self)
        else:
            new_p = And(*assumptions).implies(self)
        new_p._is_proven = True
        return new_p

    def thus_there_exists(
        self,
        existential_var: str,
        expression_to_replace: Set | SympyExpression,
        positions: list[list[int]] | None = None,
    ) -> "Exists":
        r"""
        Logical tactic.
        Given self is proven, return a new proposition that there exists an existential_var such that
        self is true, when self is expressed in terms of that existential_var.
        For example, if self is x^2 + x > 0, existential_var is y and expression_to_replace is x^2, then
        we return the proven proposition Exists y: y + x > 0.

        All occurences of the expression will be replaced according to sympy.subs.

        existential_var: str
            A new variable that is introduced into our new existential proposition.
        expression_to_replace: Set | SympyExpression
            An expression that is replaced by the new variable.
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
        assert self.is_proven, f"{self} is not proven"
        from pylogic.proposition.quantified.exists import Exists

        new_p = Exists(
            existential_var_name=existential_var,
            expression_to_replace=expression_to_replace,
            inner_proposition=self,
            positions=positions,
            _is_proven=True,
        )
        return new_p

    def thus_forall(self, quantified_arg: Set | sp.Basic) -> "Forall":
        """
        Logical tactic.
        Given self is proven, return a new proposition that for all variables, self is true.
        """
        assert self.is_proven, f"{self} is not proven"
        from pylogic.proposition.quantified.forall import Forall

        new_p = Forall(
            quantified_arg=quantified_arg,
            inner_proposition=self,
            _is_proven=True,
        )
        return new_p


if __name__ == "__main__":
    pass
