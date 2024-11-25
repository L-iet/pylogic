from __future__ import annotations

import warnings
from typing import (
    TYPE_CHECKING,
    Callable,
    Literal,
    Self,
    TypedDict,
    TypeVar,
    TypeVarTuple,
    cast,
    overload,
)

from pylogic.enviroment_settings.settings import settings

if TYPE_CHECKING:
    from pylogic import Term, Unification
    from pylogic.constant import Constant
    from pylogic.helpers import Side
    from pylogic.proposition.and_ import And
    from pylogic.proposition.contradiction import Contradiction
    from pylogic.proposition.exor import ExOr
    from pylogic.proposition.iff import Iff
    from pylogic.proposition.implies import Implies
    from pylogic.proposition.not_ import Not
    from pylogic.proposition.or_ import Or
    from pylogic.proposition.quantified.exists import Exists, ExistsInSet
    from pylogic.proposition.quantified.forall import Forall, ForallInSet
    from pylogic.proposition.relation.contains import IsContainedIn
    from pylogic.proposition.relation.equals import Equals
    from pylogic.structures.class_ import Class
    from pylogic.structures.set_ import Set
    from pylogic.symbol import Symbol
    from pylogic.variable import Variable


Props = TypeVarTuple("Props")

TProposition = TypeVar("TProposition", bound="Proposition")
UProposition = TypeVar("UProposition", bound="Proposition")
InferenceRule = TypedDict("InferenceRule", {"name": str, "arguments": list[str]})


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
    args: list[Term|Set]
        The arguments of the proposition.
    arity: int
        The number of arguments of the proposition.
    is_proven: bool
        Whether the proposition is proven.
    from_assumptions: set[Proposition]
        The assumptions that were used to deduce this proposition. Excludes self.
    """

    # order of operations for propositions (0-indexed)
    # not xor and or => <=> forall forallInSet forallSubsets exists existsInSet existsUnique
    # existsUniqueInSet existsSubset existsUniqueSubset Proposition
    _precedence = 15
    _is_wrapped = False

    # TODO: arguments are not accurate
    _inference_rules: list[InferenceRule] = [
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
        {"name": "modus_tollens", "arguments": ["Implies"]},
        {"name": "de_morgan", "arguments": []},
        {"name": "contradicts", "arguments": ["Proposition"]},
        {"name": "de_morgan", "arguments": []},
    ]

    def __init__(
        self,
        name: str,
        is_assumption: bool = False,
        is_axiom: bool = False,
        description: str = "",
        args: list[Term] | None = None,
        **kwargs,
    ) -> None:
        """
        name: str
            Name of the proposition.
        is_assumption: bool
            Whether this proposition is an assumption.
        is_axiom: bool
            Whether this proposition is an axiom. Axioms are assumptions whose
            negations are never proven.
        description: str
            A description of what this proposition is.
        args: list[Term] | None
            The arguments of the proposition. If None, we assume the proposition has no arguments.
        """
        from pylogic.helpers import (
            get_class_ns,
            get_consts,
            get_sets,
            get_vars,
            python_to_pylogic,
        )
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
        self.is_axiom: bool = is_axiom
        self.args: list[Set | Term] = list(map(python_to_pylogic, args or []))
        self.arity: int = len(self.args)
        self._is_proven: bool = _is_proven
        self.is_atomic: bool = True
        self.description: str = description
        if self.is_assumption:
            self.deduced_from: Inference | None = Inference(self)
            self.from_assumptions = set()
        elif self._is_proven:
            assert _inference is not None, "Proven propositions must have an inference"
            self.deduced_from: Inference | None = _inference
            self.from_assumptions: set[Proposition] = _assumptions or set()
        else:
            self.deduced_from: Inference | None = None
            self.from_assumptions: set[Proposition] = set()

        self.bound_vars: set[Variable] = set()  # Variables that are bound to
        # quantifiers in the proposition.

        self.is_todo: bool = False

        self.variables: set[Variable] = set()
        for a in self.args:
            self.variables.update(get_vars(a))
        self.constants: set[Constant] = set()
        for a in self.args:
            self.constants.update(get_consts(a))
        self.sets: set[Set] = set()
        for a in self.args:
            self.sets.update(get_sets(a))
        self.class_ns: set[Class] = set()
        for a in self.args:
            self.class_ns.update(get_class_ns(a))

    @property
    def symbols(self) -> set[Symbol]:
        return self.variables.union(self.constants)  # type: ignore

    @property
    def atoms(self) -> set[Symbol | Set]:
        """
        All the atomic symbols and sets in the proposition.
        """
        # TODO: Maybe include Function
        return self.symbols.union(self.sets).union(self.class_ns)

    def __eq__(self, other: object) -> bool:
        if isinstance(other, Proposition):
            return self.name == other.name and self.args == other.args
        return NotImplemented

    @property
    def inference_rules(self) -> list[str]:
        return [r["name"] for r in self._inference_rules]

    def _set_is_inferred(self, value: bool) -> None:
        """
        Used in some subclasses like IsContainedIn for custom behaviour when a proof is made
        """
        pass

    def _set_is_proven(self, value: bool) -> None:
        from pylogic.assumptions_context import assumptions_contexts

        self._is_proven = value
        if value:
            self._set_is_inferred(True)
        context = assumptions_contexts[-1]
        if context is not None and value:
            context._proven.append(self)

    def _set_is_assumption(self, value: bool) -> None:
        from pylogic.assumptions_context import assumptions_contexts

        self.is_assumption = value
        if value:
            self._set_is_inferred(True)

        context = assumptions_contexts[-1]
        if context is not None and value:
            context.assumptions.append(self)

    def _set_is_axiom(self, value: bool) -> None:
        self.is_axiom = value
        if value:
            self._set_is_inferred(True)

    def todo(self, **kwargs) -> Self:
        """
        Mark the proposition as proven, but not yet implemented.
        """
        from pylogic.inference import Inference
        from pylogic.warn import PylogicInternalWarning

        internal = kwargs.get("_internal", False)
        warning_cls = PylogicInternalWarning if internal else UserWarning

        self.is_todo = True
        warnings.warn(
            f"{self} is marked as TODO",
            warning_cls,
        )
        self._set_is_proven(True)
        self.from_assumptions = set()
        self.deduced_from = Inference(self, rule="todo")
        return self

    def assume(self) -> Self:
        """
        Mark the proposition as an assumption.
        """
        self._set_is_assumption(True)
        return self

    def eval_same(self, other: Proposition) -> bool:
        from pylogic.helpers import eval_same

        return self.name == other.name and all(
            eval_same(self_arg, other_arg)
            for self_arg, other_arg in zip(self.args, other.args)
        )

    def __hash__(self) -> int:
        return hash((self.name, *self.args))

    def __repr__(self) -> str:
        if self.args:
            args_str = tuple(str(a) for a in self.args)
            return f"Proposition({self.name}, {', '.join(args_str)})"
        else:
            return f"Proposition({self.name})"

    def __str__(self) -> str:
        if self.args:
            args_str = tuple(str(a) for a in self.args)
            return f"{self.name}({', '.join(args_str)})"
        else:
            return self.name

    def __copy__(self) -> Self:
        return self.copy()

    def __bool__(self) -> bool:
        raise TypeError("Cannot convert proposition to bool")

    def __rshift__(self, other: Proposition) -> Implies[Proposition, Proposition]:
        if settings["PYTHON_OPS_RETURN_PROPS"]:
            from pylogic.proposition.implies import Implies

            return Implies(self, other)
        return NotImplemented

    def __and__(self, other: Proposition) -> And[Proposition, Proposition]:
        if settings["PYTHON_OPS_RETURN_PROPS"]:
            from pylogic.proposition.and_ import And

            return And(self, other)
        return NotImplemented

    def __or__(self, other: Proposition) -> Or[Proposition, Proposition]:
        if settings["PYTHON_OPS_RETURN_PROPS"]:
            from pylogic.proposition.or_ import Or

            return Or(self, other)
        return NotImplemented

    def __xor__(self, other: Proposition) -> ExOr[Proposition, Proposition]:
        if settings["PYTHON_OPS_RETURN_PROPS"]:
            from pylogic.proposition.exor import ExOr

            return ExOr(self, other)
        return NotImplemented

    def __invert__(self) -> Not[Proposition]:
        if settings["PYTHON_OPS_RETURN_PROPS"]:
            from pylogic.proposition.not_ import Not

            return Not(self)
        return NotImplemented

    def _latex(self, printer=None) -> str:
        from pylogic.helpers import latex

        args_latex = [latex(a) for a in self.args]
        if not args_latex:
            return rf"\text{{{self.name}}}"
        return rf"\text{{{self.name}}}\left({', '.join(args_latex)}\right)"

    def _repr_latex_(self) -> str:
        return f"$${self._latex()}$$"

    @property
    def is_proven(self) -> bool:
        return self._is_proven or self.is_assumption or self.is_axiom

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

    def set_description(self, description: str) -> Self:
        """
        Set the description of the proposition.
        """
        self.description = description
        return self

    def set_desc(self, description: str) -> Self:
        """
        Set the description of the proposition.
        """
        return self.set_description(description)

    def copy(self) -> Self:
        """
        Create a shallow copy of the proposition.
        """
        return self.__class__(
            self.name,
            is_assumption=self.is_assumption,
            description=self.description,
            args=self.args,
            _is_proven=self._is_proven,
            _inference=self.deduced_from,
            _assumptions=self.from_assumptions,
        )

    def deepcopy(self) -> Self:
        """
        Create a deep copy of the proposition.
        """
        from pylogic.helpers import is_python_numeric

        return self.__class__(
            self.name,
            is_assumption=self.is_assumption,
            description=self.description,
            args=[a.deepcopy() if not is_python_numeric(a) else a for a in self.args],  # type: ignore
            _is_proven=self._is_proven,
            _inference=self.deduced_from,
            _assumptions=self.from_assumptions,
        )

    def replace(
        self,
        replace_dict: dict[Term, Term],
        positions: list[list[int]] | None = None,
        equal_check: Callable[[Term, Term], bool] | None = None,
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

        equal_check: Callable[[Term, Term], bool] | None
            A function that takes two arguments and returns True if they compare equal.
        """
        from pylogic.expressions.expr import Expr

        equal_check = equal_check or (lambda x, y: x == y)
        new_p_args = self.args.copy()
        index = -1
        for arg in new_p_args:
            index += 1
            if (positions is not None) and not [index] in positions:
                continue
            if isinstance(arg, Expr):
                new_p_args[index] = arg.replace(replace_dict, equal_check=equal_check)
            else:
                for current_val in replace_dict:
                    new_val = replace_dict[current_val]
                    if equal_check(current_val, arg):
                        new_p_args[index] = new_val
                        break

        new_p = self.__class__(
            self.name,
            is_assumption=False,
            args=new_p_args,
        )
        return new_p

    def substitute(self, side: Side | str, equality: "Equals", **kwargs) -> Self:
        """
        Parameters
        ----------
        side: Side
            Side.LEFT or Side.RIGHT
            The side of the equality to appear in the result
        equality: Equals
            An equality proposition. We look for the other side of the equality
            in self and replace it with the 'side'.
        """
        if self.is_proven and equality.is_proven and not kwargs:
            from pylogic.inference import Inference

            kwargs = dict(
                _is_proven=True,
                _inference=Inference(self, equality, rule="p_substitute"),
                _assumptions=get_assumptions(self).union(get_assumptions(equality)),
            )

        return equality.substitute_into(side, self, **kwargs)

    def p_substitute(self, side: Side | str, equality: Equals) -> Self:
        """
        Logical inference rule.
        Parameters
        ----------
        side: Side
            Side.LEFT or Side.RIGHT
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
        self,
        other: Implies[TProposition, UProposition],
        is_assumption: bool = False,
        **kwargs,
    ) -> Implies[And[Self, TProposition], UProposition]: ...

    @overload
    def implies(
        self, other: TProposition, is_assumption: bool = False, **kwargs
    ) -> Implies[Self, TProposition]: ...

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
            return self.and_(other.antecedent).implies(
                other.consequent, is_assumption=is_assumption, **kwargs
            )

        return Implies(self, other, is_assumption, **kwargs)

    def iff(
        self, other: TProposition, is_assumption: bool = False, **kwargs
    ) -> Iff[Self, TProposition]:
        r"""
        Create a biconditional between this proposition and another.
        """
        from pylogic.proposition.iff import Iff

        return Iff(self, other, is_assumption=is_assumption, **kwargs)

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
        from pylogic.inference import Inference
        from pylogic.proposition.and_ import And

        props = []
        first_not_proven = None
        for p in (self, *others):
            if not p.is_proven and first_not_proven is None:
                first_not_proven = p
            if isinstance(p, And):
                props.extend(p.de_nest().propositions)
            else:
                props.append(p)
        if first_not_proven is None:
            kwargs["_is_proven"] = True
            kwargs["_assumptions"] = get_assumptions(self).union(
                *[get_assumptions(o) for o in others]  # type: ignore
            )
            kwargs["_inference"] = Inference(self, *others, rule="all_proven")

        new_p = And(*props, is_assumption=is_assumption, **kwargs)  # type: ignore
        if not allow_duplicates:
            return new_p.remove_duplicates()
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
        from pylogic.inference import Inference
        from pylogic.proposition.or_ import Or

        props = []
        first_proven = None
        for p in (self, *others):
            if p.is_proven and first_proven is None:
                first_proven = p
            if isinstance(p, Or):
                props.extend(p.de_nest().propositions)
            else:
                props.append(p)
        if first_proven is not None:
            kwargs["_is_proven"] = True
            kwargs["_assumptions"] = get_assumptions(self).union(
                *[get_assumptions(o) for o in others]  # type: ignore
            )
            kwargs["_inference"] = Inference(self, *others, rule="one_proven")
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
        return first.or_(  # type: ignore
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
        from pylogic.inference import Inference
        from pylogic.proposition.exor import ExOr

        props = []
        will_be_proven = None
        for p in (self, *others):
            if p.is_proven and will_be_proven is None:
                will_be_proven = True
            elif p.is_proven:
                will_be_proven = False
            if isinstance(p, ExOr):
                props.extend(p.de_nest().propositions)
            else:
                props.append(p)
        if will_be_proven:
            kwargs["_is_proven"] = True
            kwargs["_assumptions"] = get_assumptions(self).union(
                *[get_assumptions(o) for o in others]  # type:ignore
            )
            kwargs["_inference"] = Inference(self, *others, rule="one_proven")
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
        """Logical inference rule.
        Same as and_, but returns a proven proposition when self and all others are proven.
        """
        from pylogic.inference import Inference

        assert len(others) > 0, "Must provide at least one proposition"
        assert self.is_proven, f"{self} is not proven"
        for o in others:
            assert o.is_proven, f"{o} is not proven"  # type:ignore
        all_assumptions = get_assumptions(self).union(
            *[get_assumptions(o) for o in others]  # type: ignore
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
        """Logical inference rule.
        Same as and_reverse, but returns a proven proposition when self and all others are proven.
        """
        from pylogic.inference import Inference

        assert len(others) > 0, "Must provide at least one proposition"
        assert self.is_proven, f"{self} is not proven"
        for o in others:
            assert o.is_proven, f"{o} is not proven"  # type:ignore
        all_assumptions = get_assumptions(self).union(
            *[get_assumptions(o) for o in others]  # type:ignore
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
        Logical inference rule.
        other: Implies
            Must be an implication that has been proven whose structure is
            self -> OtherProposition
        """
        from pylogic.inference import Inference
        from pylogic.proposition.implies import Implies

        assert self.is_proven, f"{self} is not proven"
        assert isinstance(other, Implies), f"{other} is not an implication"
        assert other.is_proven, f"{other} is not proven"
        assert other.antecedent == self, f"{other.antecedent} is not the same as {self}"
        new_p = other.consequent.copy()
        new_p._set_is_proven(True)
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
        Logical inference rule.
        other: Implies
            Must be an implication that has been proven whose structure is
            OtherProposition -> ~self
        """
        from pylogic.inference import Inference
        from pylogic.proposition.not_ import Not, are_negs

        assert self.is_proven, f"{self} is not proven"
        assert other.is_proven, f"{other} is not proven"
        assert are_negs(
            other.consequent, self
        ), f"{other.consequent} is not the negation of {self}"
        # I'm using copy here because neg(Not(p)) returns p,
        # and we should avoid proving p in a different place.
        if isinstance(other.antecedent, Not):
            n_other_ante = other.antecedent.negated.copy()
        else:
            n_other_ante = Not(other.antecedent)
        new_p = cast(TProposition | Not[TProposition], n_other_ante)
        new_p._set_is_proven(True)
        new_p.deduced_from = Inference(self, other, rule="modus_tollens")
        new_p.from_assumptions = get_assumptions(self).union(get_assumptions(other))
        return new_p

    def is_one_of(self, other: And, *, __recursing: bool = False) -> Self:
        r"""
        Logical inference rule.
        If we have proven other, we can prove any of the propositions in it.
        other: And
            Must be a conjunction that has been proven where one of the propositions is self.
        """
        if not __recursing:
            assert other.is_proven, f"{other} is not proven"
        from pylogic.inference import Inference
        from pylogic.proposition.and_ import And

        for p in other.propositions:
            if p == self:
                new_p = self.copy()
                new_p._set_is_proven(True)
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
        Logical inference rule.
        other: Proposition
            A proven forall proposition that implies this proposition.
        """
        # TODO: Change unification so that we cannot prove
        # P(x) from forall x: P(1).
        from pylogic.inference import Inference
        from pylogic.proposition.quantified.forall import Forall

        assert isinstance(other, Forall), f"{other} is not a forall statement"
        assert other.is_proven, f"{other} is not proven"
        unif = other.inner_proposition.unify(self)
        if (
            isinstance(unif, dict)
            and len(unif) == 1
            and list(unif.keys())[0] == other.variable
        ) or unif is True:
            new_p = self.copy()
            new_p._set_is_proven(True)
            new_p.deduced_from = Inference(self, other, rule="is_special_case_of")
            new_p.from_assumptions = get_assumptions(other).copy()
            return new_p
        raise ValueError(f"{self} is not a special case of {other}")

    @overload
    def followed_from(
        self, assumption: TProposition, **kwargs
    ) -> Implies[TProposition, Self]: ...

    @overload
    def followed_from(
        self, *assumptions: *Props, **kwargs
    ) -> Implies[And[*Props], Self]: ...

    def followed_from(self, *assumptions, **kwargs):  # type: ignore
        """
        Logical inference rule.
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
        from pylogic.warn import PylogicInternalWarning

        assert self.is_proven, f"{self} is not proven"
        _internal_tactic = kwargs.get("_internal_tactic", False)
        assert len(assumptions) > 0, "Must provide at least one other assumption"
        for a in assumptions:
            assert a.is_assumption, f"{a} is not an assumption"
            if a not in self.from_assumptions:
                if _internal_tactic:
                    warning_cls = PylogicInternalWarning
                else:
                    warning_cls = UserWarning
                warnings.warn(
                    f"{a} was not used to deduce {self}",
                    warning_cls,
                )
        from pylogic.proposition.and_ import And
        from pylogic.proposition.implies import Implies

        if len(assumptions) == 1:
            assumptions[0]._set_is_assumption(False)
            assumptions[0]._set_is_proven(False)
            new_p = cast(
                Implies[Proposition, Self], assumptions[0].implies(self)  # type: ignore
            )
        else:
            for a in assumptions:
                # this has been used to prove an implication so
                # we don't want it to be an assumption anymore
                a._set_is_assumption(False)
                a._set_is_proven(False)
            new_p = cast(Implies[And[*Props], Self], And(*assumptions).implies(self))  # type: ignore
        new_p._set_is_proven(True)
        new_p.deduced_from = Inference(
            self, *assumptions, rule="followed_from"  # type:ignore
        )
        new_p.from_assumptions = self.from_assumptions - set(assumptions)
        return new_p

    def thus_there_exists(
        self,
        existential_var: str,
        expression_to_replace: Term,
        set_: Set | Variable | Class | None = None,
        expression_to_replace_is_in_set: (
            IsContainedIn[Term, Set | Variable | Class] | None
        ) = None,
        latex_name: str | None = None,
        positions: list[list[int]] | None = None,
    ) -> Exists[Self]:
        r"""
        Logical inference rule.
        Given self is proven, return a new proposition that there exists an existential_var such that
        self is true, when self is expressed in terms of that existential_var.
        For example, if self is x^2 + x > 0, existential_var is y and expression_to_replace is x^2, then
        we return the proven proposition Exists y: y + x > 0.

        existential_var: str
            A new variable that is introduced into our new existential proposition.
        expression_to_replace: Set | SympyExpression
            An expression that is replaced by the new variable.
        set_: Set
            The set in which the existential variable is contained.
        expression_to_replace_is_in_set: IsContainedIn
            A proposition that states that the expression_to_replace is in the set_.
        latex_name: str | None
            The latex representation of the existential variable.
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
        from pylogic.helpers import find_first
        from pylogic.inference import Inference
        from pylogic.proposition.quantified.exists import Exists, ExistsInSet
        from pylogic.variable import Variable

        # Check that the expression to replace does not depend on any bound variables
        # prevent the sequence
        # forall a: P(x0(a), a) -> exists x: forall a: P(x, a)
        if isinstance(expression_to_replace, Variable):
            first_not_in_atoms_or_bound = find_first(
                lambda x: (x.is_bound),
                expression_to_replace.independent_dependencies,
            )
            if first_not_in_atoms_or_bound[1] is not None:
                raise ValueError(
                    f"{first_not_in_atoms_or_bound[1]} is not in the atoms of {self}, or is bound already, \
and is a dependency of {expression_to_replace}"
                )
        if set_ is None:
            exists_cls = Exists
        else:
            exists_cls = ExistsInSet
            if expression_to_replace_is_in_set is None:
                # try to prove by inspection
                expression_to_replace.is_in(set_).by_inspection()
            else:
                assert (
                    isinstance(expression_to_replace_is_in_set, IsContainedIn)
                    and expression_to_replace_is_in_set.left == expression_to_replace
                    and expression_to_replace_is_in_set.right == set_
                ), f"{expression_to_replace_is_in_set} is not a proof that {expression_to_replace} is in {set_}"
        new_p = exists_cls.from_proposition(
            existential_var_name=existential_var,
            expression_to_replace=expression_to_replace,
            set_=set_,
            latex_name=latex_name,
            inner_proposition=self,
            positions=positions,
            _is_proven=True,
            _inference=Inference(self, rule="thus_there_exists"),
            _assumptions=get_assumptions(self).copy(),
        )

        return new_p

    @overload
    def thus_forall(
        self,
        variable_or_containment: IsContainedIn[Term, Set | Variable | Class],
        **kwargs,
    ) -> ForallInSet[Self]: ...
    @overload
    def thus_forall(
        self,
        variable_or_containment: Variable,
        set_: Set | Variable | Class,
        **kwargs,
    ) -> ForallInSet[Self]: ...
    @overload
    def thus_forall(
        self,
        variable_or_containment: Variable,
        **kwargs,
    ) -> Forall[Self]: ...
    def thus_forall(
        self,
        variable_or_containment: Variable | IsContainedIn[Term, Set | Variable | Class],
        set_: Set | Variable | Class | None = None,
        **kwargs,
    ) -> Forall[Self] | ForallInSet[Self]:
        """
        Logical inference rule.
        Given self is proven, return a new proposition that for all variables, self is true.
        This inference rule binds the variable, so you cannot reuse the variable
        unless you unbind it.
        """
        assert self.is_proven, f"{self} is not proven"
        from pylogic.inference import Inference
        from pylogic.proposition.quantified.forall import Forall, ForallInSet
        from pylogic.proposition.relation.contains import IsContainedIn
        from pylogic.variable import Variable

        if isinstance(variable_or_containment, IsContainedIn):
            assert (
                variable_or_containment.is_assumption
            ), f"{variable_or_containment} is not an assumption"
            variable = variable_or_containment.left
            assert isinstance(variable, Variable), f"{variable} is not a variable"
            set_ = variable_or_containment.right
            cls = ForallInSet
            variable_or_containment._set_is_assumption(False)
        else:
            variable = variable_or_containment
            if set_ is not None:
                assert variable in set_, f"{variable} is not in {set_}"
            set_ = set_
            cls = Forall if set_ is None else ForallInSet
        assert variable.is_bound is False, f"{variable} is already bound"
        assert len(variable.depends_on) == 0, f"{variable} depends on something"
        return cls(
            variable=variable,
            set_=set_,  # type:ignore
            inner_proposition=self,
            _is_proven=True,
            _inference=Inference(self, rule="thus_forall"),
            _assumptions=get_assumptions(self).copy(),
            **kwargs,
        )

    def close_all_scopes(self) -> Proposition:
        """
        Logical inference rule.
        Close all scopes in the proposition.
        If assumptions (A) were used to deduce this proposition (self), they are
        removed and we get a proof of A -> self.
        If variables exist in the proposition, they are universally quantified.
        Universal quantifiers scopes are closed last so they are outermost.
        """
        from pylogic.expressions.expr import Expr
        from pylogic.variable import Variable

        # TODO: Fix this. Propoition needs to have .symbols, .sets, .functions just like Expr
        # in order for this to work correctly.

        new_p = self.followed_from(*self.from_assumptions)
        all_vars = set()
        for arg in self.args:
            if isinstance(arg, Expr):
                expr_symbols = arg.symbols
                all_vars.update(expr_symbols)
            elif isinstance(arg, Variable):
                all_vars.add(arg)
        for v in all_vars:
            new_p = new_p.thus_forall(v)
        return new_p

    def de_morgan(self) -> Self:
        """
        Apply De Morgan's law to self to return an equivalent proposition.

        In intuitionistic logic, the only valid De Morgan's laws are

        `~A and ~B <-> ~(A or B)`

        `~A or ~B -> ~(A and B)`.
        """
        return self

    def contradicts(self, other: Proposition) -> Contradiction:
        """
        Logical inference rule. If self and other are negations (and both proven),
        return a contradiction.
        """
        assert self.is_proven, f"{self} is not proven"
        assert other.is_proven, f"{other} is not proven"
        from pylogic.inference import Inference
        from pylogic.proposition.contradiction import Contradiction
        from pylogic.proposition.not_ import are_negs

        if are_negs(self, other):
            return Contradiction(
                _is_proven=True,
                _inference=Inference(self, other, rule="contradicts"),
                _assumptions=get_assumptions(self).union(get_assumptions(other)),
            )
        raise ValueError(f"{self} and {other} are not negations")

    def has_as_subproposition(self, other: Proposition) -> bool:
        """
        Check if other is a subproposition of self.
        """
        return self == other

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

        Will also unify pylogic.Expr (unevaluated expressions).
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


def predicate(name: str) -> Callable[..., Proposition]:
    """
    Create a predicate with a given name.

    A predicate is a python function that returns a proposition.
    """

    def inner(*args, **kwargs) -> Proposition:
        return Proposition(name, args=args, **kwargs)

    return inner


def prop(name: str, *args: Term, **kwargs) -> Proposition:
    """
    Create a proposition with a given name and arguments.
    """
    return Proposition(name, args=args, **kwargs)


if __name__ == "__main__":
    pass
