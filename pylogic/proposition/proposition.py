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
    from pylogic.proposition.exor import ExOr
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

    def describe(self, *, _indent=0) -> str:
        """
        Return a description of the proposition.
        """
        if self.description:
            return "  " * _indent + self.description + "\n"
        return self.as_text(_indent=_indent)

    def copy(self) -> Self:
        return self.__class__(
            self.name,
            is_assumption=self.is_assumption,
            description=self.description,
            args=self.args.copy(),  # TODO: check if we need deepcopy
            _is_proven=self._is_proven,
            _inference=self.deduced_from,
            _assumptions=self.from_assumptions,
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
        new_p_args = self.args.copy()
        index = -1
        for arg in new_p_args:
            index += 1
            if (positions is not None) and not [index] in positions:
                continue
            if arg == current_val:
                new_p_args[index] = new_val
            elif isinstance(arg, sp.Basic):
                new_p_args[index] = arg.subs(current_val, new_val)

        new_p = self.__class__(
            self.name,
            is_assumption=False,
            args=new_p_args,
        )
        return new_p

    def substitute(self, side: Side, equality: "Equals", **kwargs) -> Self:
        """
        Parameters
        ----------
        side: str
            "left" or "right"
        equality: Equals
            An equality proposition. We look for the other side of the equality
            in self and replace it with the 'side'.
        """
        return equality.substitute_into(side, self, **kwargs)

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
        new_p = self.substitute(
            side,
            equality,
            _is_proven=True,
            _inference=Inference(self, equality, rule="p_substitute"),
            _assumptions=get_assumptions(self).union(get_assumptions(equality)),
        )
        return new_p

    @overload
    def implies(
        self, other: TProposition, is_assumption: bool = False, **kwargs
    ) -> Implies[Self, TProposition]: ...

    @overload
    def implies(
        self,
        other: Implies[TProposition, UProposition],
        is_assumption: bool = False,
        **kwargs,
    ) -> Implies[And[Self, TProposition], UProposition]: ...

    def implies(
        self,
        other: TProposition | Implies[TProposition, UProposition],
        is_assumption: bool = False,
        **kwargs,
    ) -> Implies[Self, TProposition] | Implies[And[Self, TProposition], UProposition]:
        r"""
        Create an implication from this proposition to another.
        If other is an implication `A -> B`, we return an implication
        `(self /\ A) -> B`.
        """
        from pylogic.proposition.implies import Implies

        if isinstance(other, Implies):
            return self.and_(other.antecedent).implies(other.consequent)

        return Implies(self, other, is_assumption, **kwargs)

    @overload
    def and_(
        self,
        *others: *Props,
        is_assumption: bool = False,
        allow_duplicates: Literal[True] = True,
        **kwargs,
    ) -> And: ...

    @overload
    def and_(
        self,
        *others: *Props,
        is_assumption: bool = False,
        allow_duplicates: bool = False,
        **kwargs,
    ) -> And[Self, *Props]: ...

    def and_(
        self,
        *others: *Props,
        is_assumption: bool = False,
        allow_duplicates: bool = False,
        **kwargs,
    ) -> And[Self, *Props] | And:
        """
        Combine this proposition with others using a conjunction.
        Continguous `And` objects are combined into one `And` sequence to reduce
        nesting.
        allow_duplicates: bool
            If True, we do not remove duplicate propositions.
        """
        from pylogic.proposition.and_ import And

        props = []
        for p in (self, *others):
            if isinstance(p, And):
                props.extend(p.propositions)
            else:
                props.append(p)
        new_p = And(*props, is_assumption=is_assumption, **kwargs)
        if not allow_duplicates:
            return new_p.remove_duplicates()
        x = self.and_(*others, allow_duplicates=True, **kwargs)
        return new_p

    @overload
    def and_reverse(
        self,
        *others: *Props,
        is_assumption: bool = False,
        allow_duplicates: Literal[True] = True,
        **kwargs,
    ) -> And: ...

    @overload
    def and_reverse(
        self,
        *others: *Props,
        is_assumption: bool = False,
        allow_duplicates: bool = False,
        **kwargs,
    ) -> And[*Props, Self]: ...

    def and_reverse(
        self,
        *others: *Props,
        is_assumption: bool = False,
        allow_duplicates: bool = False,
        **kwargs,
    ) -> And[*Props, Self] | And:
        """
        Combine this proposition with others using a conjunction, with self at
        the end.
        Continguous `And` objects are combined into one `And` sequence to reduce
        nesting.
        allow_duplicates: bool
            If True, we do not remove duplicate propositions.
        """
        first = others[0]
        rest = others[1:]
        return first.and_(  # type:ignore
            *rest,
            self,
            is_assumption=is_assumption,
            allow_duplicates=allow_duplicates,
            **kwargs,
        )

    def or_(
        self,
        *others: *Props,
        is_assumption: bool = False,
        allow_duplicates: bool = False,
        **kwargs,
    ) -> Or[Self, *Props] | Or:
        """
        Combine this proposition with others using a disjunnction.
        Continguous `Or` objects are combined into one `Or` sequence to reduce
        nesting.
        allow_duplicates: bool
            If True, we do not remove duplicate propositions.
        """
        from pylogic.proposition.or_ import Or

        props = []
        for p in (self, *others):
            if isinstance(p, Or):
                props.extend(p.propositions)
            else:
                props.append(p)
        new_p = Or(*props, is_assumption=is_assumption, **kwargs)  # type:ignore
        if not allow_duplicates:
            return new_p.remove_duplicates()
        return new_p

    def or_reverse(
        self,
        *others: *Props,
        is_assumption: bool = False,
        allow_duplicates: bool = False,
        **kwargs,
    ) -> Or[*Props, Self] | Or:
        """
        Combine this proposition with others using a disjunction, with self at
        the end.
        Continguous `Or` objects are combined into one `Or` sequence to reduce
        nesting.
        allow_duplicates: bool
            If True, we do not remove duplicate propositions.
        """
        first = others[0]
        rest = others[1:]
        return first.or_(
            *rest,
            self,
            is_assumption=is_assumption,
            allow_duplicates=allow_duplicates,
            **kwargs,
        )

    def xor(
        self,
        *others: *Props,
        is_assumption: bool = False,
        allow_duplicates: bool = False,
        **kwargs,
    ) -> ExOr[Self, *Props] | ExOr:
        """
        Combine this proposition with others using an exclusive or.
        Continguous `ExOr` objects are combined into one `ExOr` sequence to reduce
        nesting.
        allow_duplicates: bool
            If True, we do not remove duplicate propositions.
        """
        from pylogic.proposition.exor import ExOr

        props = []
        for p in (self, *others):
            if isinstance(p, ExOr):
                props.extend(p.propositions)
            else:
                props.append(p)
        new_p = ExOr(*props, is_assumption=is_assumption, **kwargs)  # type:ignore
        if not allow_duplicates:
            return new_p.remove_duplicates()
        return new_p

    def xor_reverse(
        self,
        *others: *Props,
        is_assumption: bool = False,
        allow_duplicates: bool = False,
        **kwargs,
    ) -> ExOr[*Props, Self] | ExOr:
        """
        Combine this proposition with others using an exclusive or, with self at
        the end.
        Continguous `ExOr` objects are combined into one `ExOr` sequence to reduce
        nesting.
        allow_duplicates: bool
            If True, we do not remove duplicate propositions.
        """
        first = others[0]
        rest = others[1:]
        return first.xor(  # type:ignore
            *rest,
            self,
            is_assumption=is_assumption,
            allow_duplicates=allow_duplicates,
            **kwargs,
        )

    def p_and(
        self, *others: *Props, allow_duplicates: bool = False
    ) -> And[Self, *Props]:
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
            allow_duplicates=allow_duplicates,
            _is_proven=True,
            _assumptions=all_assumptions,
            _inference=Inference(self, *others, rule="p_and"),
        )
        return new_p

    def p_and_reverse(
        self, *others: *Props, allow_duplicates: bool = False
    ) -> And[*Props, Self]:
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
            allow_duplicates=allow_duplicates,
            _is_proven=True,
            _assumptions=all_assumptions,
            _inference=Inference(self, *others, rule="p_and_reverse"),
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
        new_p.deduced_from = Inference(self, other, rule="modus_ponens")
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
        new_p.deduced_from = Inference(self, other, rule="modus_tollens")
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
                new_p.deduced_from = Inference(self, other, rule="is_one_of")
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
        # TODO: Change unification so that we cannot prove
        # P(x) from forall x: P(1).
        from pylogic.proposition.quantified.forall import Forall
        from pylogic.inference import Inference

        assert isinstance(other, Forall), f"{other} is not a forall statement"
        assert other.is_proven, f"{other} is not proven"
        unif = other.inner_proposition.unify(self)
        if (
            isinstance(unif, dict)
            and len(unif) == 1
            and list(unif.keys())[0] == other.variable
        ) or unif is True:
            new_p = self.copy()
            new_p._is_proven = True
            new_p.deduced_from = Inference(self, other, rule="is_special_case_of")
            new_p.from_assumptions = get_assumptions(other).copy()
            return new_p
        raise ValueError(f"{self} is not a special case of {other}")

    @overload
    def followed_from(
        self, assumption: TProposition
    ) -> Implies[TProposition, Self]: ...

    @overload
    def followed_from(self, *assumptions: *Props) -> Implies[And[*Props], Self]: ...

    def followed_from(self, *assumptions):  # type: ignore
        """
        Logical tactic.
        Given self is proven, return a new proposition that is an implication of
        the form And(*assumptions) -> self.
        *assumptions: Proposition
            Propositions that implied this proposition.
        This function only accepts propositions that were explicitly declared as
        assumptions and used to deduce self.

        **Note** that after this function is called, the assumptions are no longer
        considered assumptions. You would need to assume them again if you want to
        use them in another deduction.
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
            assumptions[0].is_assumption = False
            new_p = cast(
                Implies[Proposition, Self], assumptions[0].copy().implies(self)  # type: ignore
            )
            new_p.antecedent.is_assumption = False
            new_p.antecedent._is_proven = False
        else:
            a_s = []
            for a in assumptions:
                # this has been used to prove an implication so
                # we don't want it to be an assumption anymore
                a.is_assumption = False
                new_a = a.copy()  # type: ignore
                new_a.is_assumption = False
                new_a._is_proven = False
                a_s.append(new_a)
            new_p = cast(Implies[And[*Props], Self], And(*a_s).implies(self))  # type: ignore
        new_p._is_proven = True
        new_p.deduced_from = Inference(self, *assumptions, rule="followed_from")
        new_p.from_assumptions = set()
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
            _inference=Inference(self, rule="thus_there_exists"),
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
        from pylogic.inference import Inference

        new_p = Forall(
            variable=variable,
            inner_proposition=self,
            _is_proven=True,
            _inference=Inference(self, rule="thus_forall"),
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
