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
    from pylogic.structures.sets import Set
    from pylogic.proposition.relation.equals import Equals
    from pylogic.proposition.and_ import And
    from pylogic.proposition.or_ import Or
    from pylogic.proposition.implies import Implies
    from pylogic.proposition.quantified.exists import Exists
    from pylogic.proposition.quantified.forall import Forall
    from pylogic.proposition.not_ import Not
    from pylogic.proposition.contradiction import Contradiction
    from pylogic.variable import Variable
    from pylogic.structures.sets import Set
    from pylogic.symbol import Symbol

    Term = Symbol | Set | sp.Basic | int | float
    Unification = dict[Variable, Term]


Props = TypeVarTuple("Props")

Side = Literal["left", "right"]

latex_printer = LatexPrinter()
TProposition = TypeVar("TProposition", bound="Proposition")
UProposition = TypeVar("UProposition", bound="Proposition")
Tactic = TypedDict("Tactic", {"name": str, "arguments": list[str]})


####################################################


def get_assumptions(p: Proposition) -> set[Proposition]:
    """
    Given a proposition, return the assumptions that were used to deduce it.
    """
    if p.is_assumption:
        return {p}
    return p.from_assumptions


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
        {"name": "de_morgan", "arguments": []},
    ]

    def __init__(
        self,
        name: str,
        is_assumption: bool = False,
        description: str = "",
        args: list[Term] | None = None,
        **kwargs,
    ) -> None:
        """
        name: str
            Name of the proposition.
        is_assumption: bool
            Whether this proposition is an assumption.
        description: str
            A description of what this proposition is.
        args: list[Set | SympyExpression] | None
            The arguments of the proposition. If None, we assume the proposition has no arguments.

        """
        from pylogic.inference import Inference

        _is_proven: bool = cast(bool, kwargs.get("_is_proven", False))
        _inference: Inference | None = cast(
            Inference | None, kwargs.get("_inference", None)
        )
        _assumptions: set[Proposition] | None = cast(
            set[Proposition] | None, kwargs.get("_assumptions", None)
        )
        name = name.strip()
        assert set(name.split("_")) != {""}, "Proposition name cannot be empty"
        self.name: str = name
        self.is_assumption: bool = is_assumption
        self.args: list[Set | Term] = args or []
        self.arity: int = len(self.args)
        self._is_proven: bool = _is_proven
        self.is_atomic: bool = True
        self.description: str = description
        if self.is_assumption:
            self.deduced_from: Inference | None = Inference(self)
            self.from_assumptions = set()
        elif self._is_proven:
            assert _inference is not None, "Proven propositions must have an inference"
            assert _assumptions is not None, "Proven propositions must have assumptions"
            self.deduced_from: Inference | None = _inference
            self.from_assumptions: set[Proposition] = _assumptions
        else:
            self.deduced_from: Inference | None = None
            self.from_assumptions: set[Proposition] = set()

    def __eq__(self, other: object) -> bool:
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

    def __copy__(self) -> Self:
        return self.copy()

    def _latex(self, printer=latex_printer) -> str:
        return rf"\text{{{self.name}}} {self.args}"

    def _repr_latex_(self) -> str:
        return f"$${self._latex()}$$"

    @property
    def is_proven(self) -> bool:
        return self._is_proven or self.is_assumption

    def as_text(self, *, _indent=0) -> str:
        """
        Return a textual representation of the proposition. Subpropositions
        are indented further right. One indentation is 2 spaces.
        """
        return "  " * _indent + repr(self) + "\n"

    def copy(self) -> Self:
        return self.__class__(
            self.name,
            self.is_assumption,
            description=self.description,
            args=self.args.copy(),  # TODO: check if we need deepcopy
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

    def p_substitute(self, side: Side, equality: Equals) -> Self:
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
        from pylogic.inference import Inference

        assert self.is_proven, f"{self} is not proven"
        assert equality.is_proven, f"{equality} is not proven"
        new_p = self.substitute(side, equality)
        new_p._is_proven = True
        new_p.deduced_from = Inference(self, equality, "p_substitute")
        new_p.from_assumptions = get_assumptions(self).union(get_assumptions(equality))
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
        **kwargs,
    ) -> And[Self, *Props]:
        from pylogic.proposition.and_ import And

        return And(self, *others, is_assumption=is_assumption, **kwargs)

    def and_reverse(
        self,
        *others: *Props,
        is_assumption: bool = False,
        **kwargs,
    ) -> And[*Props, Self]:
        from pylogic.proposition.and_ import And

        return And(*others, self, is_assumption=is_assumption, **kwargs)

    def or_(
        self,
        *others: *Props,
        is_assumption: bool = False,
        **kwargs,
    ) -> Or[Self, *Props]:
        from pylogic.proposition.or_ import Or

        return Or(self, *others, is_assumption=is_assumption, **kwargs)

    def or_reverse(
        self, *others: *Props, is_assumption: bool = False, **kwargs
    ) -> Or[*Props, Self]:
        from pylogic.proposition.or_ import Or

        return Or(*others, self, is_assumption=is_assumption, **kwargs)

    def p_and(self, *others: *Props) -> And[Self, *Props]:
        """Logical tactic.
        Same as and_, but returns a proven proposition when self and all others are proven.
        """
        from pylogic.inference import Inference

        assert len(others) > 0, "Must provide at least one proposition"
        assert self.is_proven, f"{self} is not proven"
        for o in others:
            assert o.is_proven, f"{o} is not proven"  # type:ignore
        all_assumptions = get_assumptions(self).union(
            *[get_assumptions(o) for o in others]
        )
        new_p = self.and_(
            *others,
            _is_proven=True,
            _assumptions=all_assumptions,
            _inference=Inference(self, *others, "p_and"),
        )
        return new_p

    def p_and_reverse(self, *others: *Props) -> And[*Props, Self]:
        """Logical tactic.
        Same as and_reverse, but returns a proven proposition when self and all others are proven.
        """
        from pylogic.inference import Inference

        assert len(others) > 0, "Must provide at least one proposition"
        assert self.is_proven, f"{self} is not proven"
        for o in others:
            assert o.is_proven, f"{o} is not proven"  # type:ignore
        all_assumptions = get_assumptions(self).union(
            *[get_assumptions(o) for o in others]
        )
        new_p = self.and_reverse(
            *others,
            _is_proven=True,
            _assumptions=all_assumptions,
            _inference=Inference(self, *others, "p_and_reverse"),
        )
        return new_p

    def modus_ponens(self, other: Implies[Self, TProposition]) -> TProposition:
        """
        Logical tactic.
        other: Implies
            Must be an implication that has been proven whose structure is
            self.name -> OtherProposition
        """
        from pylogic.proposition.implies import Implies
        from pylogic.inference import Inference

        assert self.is_proven, f"{self} is not proven"
        assert isinstance(other, Implies), f"{other} is not an implication"
        assert other.is_proven, f"{other} is not proven"
        assert other.antecedent == self, f"{other} does not imply {self}"
        new_p = other.consequent.copy()
        new_p._is_proven = True
        new_p.deduced_from = Inference(self, other, "modus_ponens")
        new_p.from_assumptions = get_assumptions(self).union(get_assumptions(other))
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
        from pylogic.inference import Inference
        from pylogic.proposition.not_ import neg, are_negs
        from pylogic.proposition.not_ import Not

        assert self.is_proven, f"{self} is not proven"
        assert other.is_proven, f"{other} is not proven"
        assert are_negs(
            other.consequent, self
        ), f"{other.consequent} is not the negation of {self}"
        new_p = cast(TProposition | Not[TProposition], neg(other.antecedent.copy()))
        new_p._is_proven = True
        new_p.deduced_from = Inference(self, other, "modus_tollens")
        new_p.from_assumptions = get_assumptions(self).union(get_assumptions(other))
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
        from pylogic.inference import Inference

        for p in other.propositions:
            if p == self:
                new_p = self.copy()
                new_p._is_proven = True
                new_p.deduced_from = Inference(self, other, "is_one_of")
                new_p.from_assumptions = get_assumptions(other).copy()
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
        from pylogic.inference import Inference

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
        new_p.deduced_from = Inference(self, other, "is_special_case_of")
        new_p.from_assumptions = get_assumptions(other).copy()
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
        And(*assumptions) -> self.
        *assumptions: Proposition
            Propositions that implied this proposition.
        This function only accepts propositions that were explicitly declared as assumptions.
        """
        from pylogic.inference import Inference

        assert self.is_proven, f"{self} is not proven"
        assert len(assumptions) > 0, "Must provide at least one other assumption"
        for a in assumptions:
            assert a.is_assumption, f"{a} is not an assumption"  # type: ignore
            assert a in self.from_assumptions, f"{a} was not used to deduce {self}"
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
        new_p.deduced_from = Inference(self, *assumptions, "followed_from")
        new_p.from_assumptions = {
            a for a in assumptions
        }  # I think this is technically unnecessary
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
        from pylogic.inference import Inference

        new_p = Exists.from_proposition(
            existential_var_name=existential_var,
            expression_to_replace=expression_to_replace,
            inner_proposition=self,
            positions=positions,
            _is_proven=True,
            _inference=Inference(self, "thus_there_exists"),
            _assumptions=get_assumptions(self).copy(),
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
            _inference=Inference(self, "thus_forall"),
            _assumptions=get_assumptions(self).copy(),
        )
        return new_p

    def de_morgan(self) -> Self:
        """
        Apply De Morgan's law to self to return an equivalent proposition.
        """
        return self.copy()

    def contradicts(self, other: Proposition) -> Contradiction:
        """
        Logical tactic. If self and other are negations (and both proven),
        return a contradiction.
        """
        assert self.is_proven, f"{self} is not proven"
        assert other.is_proven, f"{other} is not proven"
        from pylogic.proposition.not_ import are_negs
        from pylogic.inference import Inference
        from pylogic.proposition.contradiction import Contradiction

        if are_negs(self, other):
            return Contradiction(
                _is_proven=True,
                _inference=Inference(self, other, rule="contradicts"),
                _assumptions=get_assumptions(self).union(get_assumptions(other)),
            )
        raise ValueError(f"{self} and {other} are not negations")

    def unify(self, other: Proposition) -> Unification | Literal[True] | None:
        """
        Algorithm to unify two propositions.
        If unification succeeds, a dictionary of values to instantiate variables
        to is returned.
        The dictionary never instantiates a variable `y` to variable `y`.
        It may instantiate a variable `y` to variable `x` or a variable
        `y` to a symbol or value `y`.
        If no instantiations need to be made (eg propositions are equal),
        return True.
        Otherwise (unification fails), return None.

        This does not try to unify terms or expressions, only Propositions.
        """
        if not isinstance(other, Proposition):
            raise TypeError(f"{other} is not a proposition")
        assert (
            self.is_atomic and other.is_atomic
        ), f"{self} and {other} are not atomic sentences"
        from pylogic.helpers import unify as term_unify

        if self.name != other.name or len(self.args) != len(other.args):
            return None
        d: Unification = {}
        for s_arg, o_arg in zip(self.args, other.args):
            res = term_unify(s_arg, o_arg)
            if isinstance(res, dict):
                # technically this loop should only run once
                for k in res:
                    if k in d and d[k] != res[k]:
                        return None
                    d[k] = res[k]
            elif res is None:
                return None
        if len(d) == 0:
            return True
        else:
            return d


if __name__ == "__main__":
    pass
