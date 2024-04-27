from __future__ import annotations
from typing import Self

import sympy as sp
from sympy.printing.latex import LatexPrinter

from typing import (
    TYPE_CHECKING,
    Literal,
    TypeVar,
    TypedDict,
    TypeVarTuple,
    overload,
    cast,
)

if TYPE_CHECKING:
    from pylogic.set.sets import Set
    from pylogic.proposition.relation.equals import Equals
    from pylogic.proposition.and_ import And
    from pylogic.proposition.implies import Implies
    from pylogic.proposition.quantified.exists import Exists
    from pylogic.proposition.quantified.forall import Forall
    from pylogic.proposition.not_ import Not
    from pylogic.variable import Variable
    from pylogic.set.sets import Set
    from pylogic.symbol import Symbol

    Term = Variable | Symbol | Set | sp.Basic | int | float
    Unification = dict[Variable, Term]


Props = TypeVarTuple("Props")

Side = Literal["left", "right"]

latex_printer = LatexPrinter()
TProposition = TypeVar("TProposition", bound="Proposition")
UProposition = TypeVar("UProposition", bound="Proposition")
Tactic = TypedDict("Tactic", {"name": str, "arguments": list[str]})


####################################################


class Proposition:
    """
    Attributes
    ----------
    name: str
        Name of the proposition. Typically the first part of the __repr__.
    is_assumption: bool
        Whether this proposition is an assumption.
    args: list[Term] | None
        The arguments of the proposition. If None, we assume the proposition has no arguments.
    arity: int
        The number of arguments of the proposition.
    is_proven: bool
        Whether the proposition is proven.
    """

    tactics: list[Tactic] = [
        {"name": "p_substitute", "arguments": ["Side", "Equality"]},
        {"name": "p_and", "arguments": []},
        {"name": "p_and_reverse", "arguments": []},
        {"name": "modus_ponens", "arguments": ["Implies"]},
        {"name": "is_one_of", "arguments": ["And"]},
        {"name": "is_special_case_of", "arguments": ["Forall"]},
        {"name": "followed_from", "arguments": []},
        {"name": "thus_there_exists", "arguments": ["str", "Term", "list[list[int]]"]},
        {"name": "thus_forall", "arguments": ["Variable"]},
    ]

    def __init__(
        self,
        name: str,
        is_assumption: bool = False,
        args: list[Term] | None = None,
        # completed_args: dict[str, Set | SympyExpression] | None = None,
        # completed_args_order: list[str] | None = None,
        # show_arg_position_names: bool = False,
        _is_proven: bool = False,
    ) -> None:
        """
        name: str
            Name of the proposition. Typically the first part of the __repr__.
        is_assumption: bool
            Whether this proposition is an assumption.
        args: list[Set | SympyExpression] | None
            The arguments of the proposition. If None, we assume the proposition has no arguments.

        """
        name = name.strip()
        assert set(name.split("_")) != {""}, "Proposition name cannot be empty"
        self.name: str = name
        self.is_assumption: bool = is_assumption
        self.args: list[Set | Term] = args or []
        self.arity: int = len(self.args)
        self._is_proven: bool = _is_proven
        self.is_atomic: bool = (
            True  # TODO: add is_atomic for other subclasses of Proposition
        )

    def __eq__(self, other: Proposition) -> bool:
        if isinstance(other, Proposition):
            return self.name == other.name and self.args == other.args
        return False

    def __hash__(self) -> int:
        return hash((self.name, *self.args))

    def __repr__(self) -> str:
        if self.args:
            return f"{self.name} {tuple(self.args)}"
        else:
            return self.name

    def __copy__(self) -> "Proposition":
        return self.copy()

    def _latex(self, printer=latex_printer) -> str:
        return rf"\text{{{self.name}}} {self.args}"

    def _repr_latex_(self) -> str:
        return f"$${self._latex()}$$"

    @property
    def is_proven(self) -> bool:
        return self._is_proven or self.is_assumption

    def copy(self) -> Self:
        return self.__class__(
            self.name,
            self.is_assumption,
            self.args.copy(),  # TODO: check if we need deepcopy
            _is_proven=self.is_proven,
        )

    def replace(
        self,
        current_val: Term,
        new_val: Term,
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
        for arg in new_p.args:
            index += 1
            if (positions is not None) and not [index] in positions:
                continue
            if arg == current_val:
                new_p.args[index] = new_val
            elif isinstance(arg, sp.Basic):
                new_p.args[index] = arg.subs(current_val, new_val)

        new_p._is_proven = False
        return new_p

    def substitute(self, side: Side, equality: "Equals") -> Self:
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

    def p_substitute(self, side: Side, equality: "Equals") -> Self:
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
        other: TProposition,
        is_assumption: bool = False,
    ) -> Implies[Self, TProposition]:
        from pylogic.proposition.implies import Implies

        return Implies(self, other, is_assumption)

    def and_(
        self,
        *others: *Props,
        is_assumption: bool = False,
    ) -> And[Self, *Props]:
        from pylogic.proposition.and_ import And

        return And(self, *others, is_assumption=is_assumption)

    def and_reverse(
        self, *others: *Props, is_assumption: bool = False
    ) -> And[*Props, Self]:
        from pylogic.proposition.and_ import And

        return And(*others, self, is_assumption=is_assumption)

    def p_and(self, *others: *Props) -> And[Self, *Props]:
        """Logical tactic.
        Same as and_, but returns a proven proposition when self and all others are proven.
        """
        assert len(others) > 0, "Must provide at least one proposition"
        assert self.is_proven, f"{self} is not proven"
        for o in others:
            assert o.is_proven, f"{o} is not proven"  # type:ignore
        new_p = self.and_(*others)
        new_p._is_proven = True
        return new_p

    def p_and_reverse(self, *others: *Props) -> And[*Props, Self]:
        """Logical tactic.
        Same as and_reverse, but returns a proven proposition when self and all others are proven.
        """
        assert len(others) > 0, "Must provide at least one proposition"
        assert self.is_proven, f"{self} is not proven"
        for o in others:
            assert o.is_proven, f"{o} is not proven"  # type:ignore
        new_p = self.and_reverse(*others)
        new_p._is_proven = True
        return new_p

    def modus_ponens(self, other: Implies[Self, TProposition]) -> TProposition:
        """
        Logical tactic.
        other: Implies
            Must be an implication that has been proven whose structure is
            self.name -> OtherProposition
        """
        from pylogic.proposition.implies import Implies

        assert self.is_proven, f"{self} is not proven"
        assert isinstance(other, Implies), f"{other} is not an implication"
        assert other.is_proven, f"{other} is not proven"
        assert other.antecedent == self, f"{other} does not imply {self}"
        new_p = other.consequent.copy()
        new_p._is_proven = True
        return new_p

    @overload
    def modus_tollens(
        self, other: Implies[Not[TProposition], Not[Self]]
    ) -> TProposition: ...

    @overload
    def modus_tollens(
        self, other: Implies[TProposition, Not[Self]]
    ) -> Not[TProposition]: ...

    def modus_tollens(
        self,
        other: Implies[Not[TProposition], Not[Self]] | Implies[TProposition, Not[Self]],
    ) -> TProposition | Not[TProposition]:
        """
        Logical tactic.
        other: Implies
            Must be an implication that has been proven whose structure is
            OtherProposition -> ~self
        """
        from pylogic.proposition.not_ import neg, are_negs
        from pylogic.proposition.not_ import Not

        assert self.is_proven, f"{self} is not proven"
        assert other.is_proven, f"{other} is not proven"
        assert are_negs(
            other.consequent, self
        ), f"{other.consequent} is not the negation of {self}"
        new_p = cast(TProposition | Not[TProposition], neg(other.antecedent.copy()))
        new_p._is_proven = True
        return new_p

    def is_one_of(self, other: And, *, __recursing: bool = False) -> Self:
        r"""
        Logical tactic.
        If we have proven other, we can prove any of the propositions in it.
        other: And
            Must be a conjunction that has been proven where one of the propositions is self.
        """
        if not __recursing:
            assert other.is_proven, f"{other} is not proven"
        from pylogic.proposition.and_ import And

        for p in other.propositions:
            if p == self:
                new_p = self.copy()
                new_p._is_proven = True
                return new_p
            elif isinstance(p, And):
                try:
                    return self.is_one_of(p, __recursing=True)
                except ValueError:
                    continue
        raise ValueError(f"{self} is not in {other}")

    def is_special_case_of(self, other: Forall[Self]) -> Self:
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
            and self.arity == other.inner_proposition.arity
        ), f"{self} is not a special case of {other}"

        # last case: if the inner proposition is a proposition, we check to see
        # if the self args matches inner proposition args
        value_in_self: Term | Set | None = None
        if isinstance(other.inner_proposition, Proposition):
            for tself, tother in zip(self.args, other.inner_proposition.args):
                if tother == other.variable:
                    if value_in_self is None:
                        value_in_self = tself
                    elif value_in_self != tself:
                        raise ValueError(
                            f"{self} is not a special case of {other}: {value_in_self} != {tself}"
                        )
                elif tother != tself:
                    raise ValueError(
                        f"{self} is not a special case of {other}: {tself} != {tother}"
                    )

        new_p = self.copy()
        new_p._is_proven = True
        return new_p

    @overload
    def followed_from(
        self, assumption: TProposition
    ) -> Implies[TProposition, Self]: ...

    @overload
    def followed_from(self, *assumptions: *Props) -> Implies[And[*Props], Self]: ...

    def followed_from(self, *assumptions):  # type: ignore
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
            assert a.is_assumption, f"{a} is not an assumption"  # type: ignore
        from pylogic.proposition.and_ import And
        from pylogic.proposition.implies import Implies

        if len(assumptions) == 1:
            new_p = cast(
                Implies[Proposition, Self], assumptions[0].copy().implies(self)  # type: ignore
            )
            new_p.antecedent.is_assumption = False
            new_p.antecedent._is_proven = False
        else:
            a_s = []
            for a in assumptions:
                new_a = a.copy()  # type: ignore
                new_a.is_assumption = False
                new_a._is_proven = False
                a_s.append(new_a)
            new_p = cast(Implies[And[*Props], Self], And(*a_s).implies(self))  # type: ignore
        new_p._is_proven = True
        return new_p

    def thus_there_exists(
        self,
        existential_var: str,
        expression_to_replace: Term,
        positions: list[list[int]] | None = None,
    ) -> Exists[Self]:
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

        new_p = Exists.from_proposition(
            existential_var_name=existential_var,
            expression_to_replace=expression_to_replace,
            inner_proposition=self,
            positions=positions,
            _is_proven=True,
        )
        return new_p

    def thus_forall(self, variable: Variable) -> Forall[Self]:
        """
        Logical tactic.
        Given self is proven, return a new proposition that for all variables, self is true.
        """
        assert self.is_proven, f"{self} is not proven"
        from pylogic.proposition.quantified.forall import Forall

        new_p = Forall(
            variable=variable,
            inner_proposition=self,
            _is_proven=True,
        )
        return new_p

    def unify(self, other: Proposition) -> Unification | Literal[True] | None:
        if not isinstance(other, Proposition):
            raise TypeError(f"{other} is not a proposition")
        pass


if __name__ == "__main__":
    pass
