# pyright: reportInvalidTypeForm=false
from __future__ import annotations

from typing import TYPE_CHECKING, Callable, Generic, Literal, Self, TypedDict, TypeVar

from pylogic.helpers import find_first
from pylogic.inference import Inference
from pylogic.proposition.proposition import Proposition, get_assumptions
from pylogic.typing import Term, Unification

if TYPE_CHECKING:
    from sympy.logic.boolalg import Implies as SpImplies

    from pylogic.proposition.and_ import And
    from pylogic.proposition.or_ import Or
    from pylogic.structures.class_ import Class

TProposition = TypeVar("TProposition", bound="Proposition")
UProposition = TypeVar("UProposition", bound="Proposition")
VProposition = TypeVar("VProposition", bound="Proposition")
InferenceRule = TypedDict("InferenceRule", {"name": str, "arguments": list[str]})


class Implies(Proposition, Generic[TProposition, UProposition]):
    # order of operations for propositions (0-indexed)
    # not xor and or => <=> forall forallInSet forallSubsets exists existsInSet existsUnique
    # existsUniqueInSet existsSubset existsUniqueSubset Proposition
    _precedence = 4

    _inference_rules: list[InferenceRule] = [
        {"name": "hypothetical_syllogism", "arguments": ["Implies"]},
        {"name": "impl_elim", "arguments": []},
        {"name": "definite_clause_resolve", "arguments": ["Proposition"]},
        {"name": "unit_definite_clause_resolve", "arguments": ["Proposition"]},
        {"name": "first_unit_definite_clause_resolve", "arguments": ["Proposition"]},
        {"name": "contrapositive", "arguments": []},
    ]

    def __init__(
        self,
        antecedent: TProposition,
        consequent: UProposition,
        is_assumption: bool = False,
        description: str = "",
        **kwargs,
    ) -> None:
        self.antecedent = antecedent
        self.consequent = consequent
        self.left = antecedent
        self.right = consequent
        name = f"{antecedent.name} -> {consequent.name}"
        super().__init__(name, is_assumption, description=description, **kwargs)
        self.is_atomic = False
        self.bound_vars = antecedent.bound_vars.union(consequent.bound_vars)
        self.variables = antecedent.variables.union(consequent.variables)
        self.constants = antecedent.constants.union(consequent.constants)
        self.sets = antecedent.sets.union(consequent.sets)
        self.class_ns: set[Class] = antecedent.class_ns.union(consequent.class_ns)
        self._set_init_inferred_attrs()

    def __eq__(self, other: Proposition) -> bool:
        if isinstance(other, Implies):
            return (
                self.antecedent == other.antecedent
                and self.consequent == other.consequent
            )
        return NotImplemented

    def __hash__(self) -> int:
        return hash(("impl", self.antecedent, self.consequent))

    def __str__(self) -> str:
        from pylogic.enviroment_settings.settings import settings

        if settings["SHOW_ALL_PARENTHESES"]:
            wrap = lambda p: f"({p})" if not p.is_atomic else str(p)
        else:
            wrap = lambda p: (
                f"({p})"
                if not p.is_atomic
                and p.__class__._precedence >= self.__class__._precedence
                else str(p)
            )
        return f"{wrap(self.antecedent)} -> {wrap(self.consequent)}"

    def __repr__(self) -> str:
        return f"Implies({self.antecedent!r}, {self.consequent!r})"

    def __call__(self, *props: Proposition):
        return self.definite_clause_resolve(props)

    def _latex(self, printer=None) -> str:
        from pylogic.enviroment_settings.settings import settings

        if settings["SHOW_ALL_PARENTHESES"]:
            wrap = lambda p: (
                rf"\left({p._latex()}\right)" if not p.is_atomic else p._latex()
            )
        else:
            wrap = lambda p: (
                rf"\left({p._latex()}\right)"
                if not p.is_atomic
                and p.__class__._precedence >= self.__class__._precedence
                else p._latex()
            )
        return rf"{wrap(self.antecedent)} \rightarrow {wrap(self.consequent)}"

    def copy(self) -> Self:
        return self.__class__(
            self.antecedent,
            self.consequent,
            is_assumption=self.is_assumption,
            description=self.description,
            _is_proven=self._is_proven,
            _assumptions=self.from_assumptions,
            _inference=self.deduced_from,
        )

    def deepcopy(self) -> Self:
        return self.__class__(
            self.antecedent.deepcopy(),
            self.consequent.deepcopy(),
            is_assumption=self.is_assumption,
            description=self.description,
            _is_proven=self._is_proven,
            _assumptions=self.from_assumptions,
            _inference=self.deduced_from,
        )

    def as_text(self, *, _indent=0) -> str:
        """
        Return a text representation of the proposition.
        """
        return (
            "  " * _indent
            + "if\n"
            + self.antecedent.as_text(_indent=_indent + 1)
            + "  " * _indent
            + "then\n"
            + self.consequent.as_text(_indent=_indent + 1)
        )

    def describe(self, *, _indent=0) -> str:
        """
        Return a description of the proposition.
        """
        if self.description:
            return "  " * _indent + self.description + "\n"
        return (
            "  " * _indent
            + "if\n"
            + self.antecedent.describe(_indent=_indent + 1)
            + "  " * _indent
            + "then\n"
            + self.consequent.describe(_indent=_indent + 1)
        )

    def replace(
        self,
        replace_dict: dict[Term, Term],
        positions: list[list[int]] | None = None,
        equal_check: Callable[[Term, Term], bool] | None = None,
    ) -> "Implies":
        if positions is not None:
            ante_positions = [p[1:] for p in positions if p[0] == 0]
            cons_positions = [p[1:] for p in positions if p[0] == 1]
            ante_positions = None if [] in ante_positions else ante_positions
            cons_positions = None if [] in cons_positions else cons_positions
        else:
            ante_positions = None
            cons_positions = None
        new_p = self.__class__(
            self.antecedent.replace(
                replace_dict, ante_positions, equal_check=equal_check
            ),
            self.consequent.replace(
                replace_dict, cons_positions, equal_check=equal_check
            ),
            _is_proven=False,
        )
        return new_p

    def contrapositive(self) -> Implies[Proposition, Proposition]:
        r"""Logical inference rule. Given self (`A -> B`) is proven, return the corresponding
        contrapositive (`~B -> ~A`)
        """
        from pylogic.proposition.not_ import neg

        assert self.is_proven, f"{self} is not proven"
        return Implies(
            neg(self.consequent),
            neg(self.antecedent),
            _is_proven=True,
            _assumptions=get_assumptions(self),
            _inference=Inference(self, rule="contrapositive"),
        )

    def by_inspection_check(self) -> bool | None:
        return self.antecedent == self.consequent or None

    def hypothetical_syllogism(self, *others: Implies) -> Implies:
        """
        Logical inference rule. If self is A->B, and others are
        B->C, C->D, ..., Y->Z, return A->Z.

        The antecedent of the next proposition must be the consequent of the previous one.
        """
        assert self.is_proven, f"{self} is not proven"
        assert len(others) > 0, "No propositions given"
        curr_consequent = self.consequent
        curr_prop = self
        for other in others:
            assert isinstance(other, Implies), f"{other} is not an implication"
            assert other.is_proven, f"{other} is not proven"
            assert (
                curr_consequent == other.antecedent
            ), f"Does not follow logically: {curr_prop},  {other}"
            curr_consequent = other.consequent
            curr_prop = other
        i = Implies(
            self.antecedent,
            others[-1].consequent,
            _is_proven=True,
            _assumptions=get_assumptions(self).union(get_assumptions(other)),
            _inference=Inference(self, other, rule="hypothetical_syllogism"),
        )
        return i

    def impl_to_or(self) -> Or:
        r"""Logical inference rule. Given self (`A -> B`) is proven, return the corresponding
        disjunction form (`~A \/ B`).

        This only works in classical logic, and will raise an error otherwise.
        Set pylogic.enviroment_settings.settings.settings["USE_CLASSICAL_LOGIC"] = True to use this.
        """
        assert self.is_proven, f"{self} is not proven"
        from pylogic.enviroment_settings.settings import settings
        from pylogic.proposition.not_ import neg
        from pylogic.proposition.or_ import Or

        assert settings["USE_CLASSICAL_LOGIC"], "Classical logic is not enabled"
        return Or(
            neg(self.antecedent),
            self.consequent,
            _is_proven=True,
            _assumptions=get_assumptions(self),
            _inference=Inference(self, rule="impl_to_or"),
        )

    def definite_clause_resolve(
        self,
        in_body: list[Proposition] | tuple[Proposition, ...] | And[Proposition, ...],
        **kwargs,
    ) -> Self | Implies[Proposition, UProposition] | UProposition:
        r"""
        Logical inference rule. Given self `(A /\ B /\ C...) -> D` is proven, and
        given a conjunction (or list representing a conjunction) of some props
        in the antecedent (say A and B) is proven, return a proof of the new
        definite clause `(C /\ ...) -> D` or `C -> D` if only C is left in
        the body, or D if the antecedent is left empty.
        """
        dont_prove = kwargs.get("prove", True) is False
        if not dont_prove:
            assert self.is_proven, f"{self} is not proven"
        from pylogic.proposition.and_ import And

        if not isinstance(self.antecedent, And):
            assert isinstance(
                in_body, (list, tuple)
            ), f"{in_body} should be a list/tuple since the antecedent is not an And"
            return in_body[0].modus_ponens(self, **kwargs)  # type: ignore

        in_body_is_and = isinstance(in_body, And)
        props = set(in_body.propositions if in_body_is_and else in_body)

        if in_body_is_and:
            if not dont_prove:
                assert in_body.is_proven, f"{in_body} is not proven"
                in_body_assumptions = get_assumptions(in_body)
        else:
            assert isinstance(
                in_body, (list, tuple)
            ), f"{in_body} is not a list or tuple"
            in_body_assumptions: set[Proposition] = set()
            if not dont_prove:
                for prop in props:
                    assert prop.is_proven, f"{prop} is not proven"
                    in_body_assumptions = in_body_assumptions.union(
                        get_assumptions(prop)
                    )

        rem_props = [prop for prop in self.antecedent.propositions if prop not in props]

        if len(rem_props) == 1:
            if dont_prove:
                return Implies(
                    rem_props[0],
                    self.consequent,
                )
            ret_val = Implies(
                rem_props[0],
                self.consequent,
                _is_proven=True,
                _assumptions=get_assumptions(self).union(in_body_assumptions),
            )
            ret_val.deduced_from = Inference(
                self, *props, conclusion=ret_val, rule="definite_clause_resolve"
            )
            return ret_val
        if len(rem_props) == 0:
            new_p = self.consequent.copy()
            if not dont_prove:
                new_p._set_is_proven(True)
                new_p.deduced_from = Inference(
                    self, *props, conclusion=new_p, rule="definite_clause_resolve"
                )
                new_p.from_assumptions = get_assumptions(self).union(
                    in_body_assumptions
                )
            return new_p
        if dont_prove:
            return Implies(
                And(*rem_props),  # type: ignore
                self.consequent,
            )
        new_p = Implies(
            And(*rem_props),  # type: ignore
            self.consequent,
            _is_proven=True,
            _assumptions=get_assumptions(self).union(in_body_assumptions),
        )
        new_p.deduced_from = Inference(
            self, *props, conclusion=new_p, rule="definite_clause_resolve"
        )
        return new_p  # type:ignore

    def unit_definite_clause_resolve(
        self, in_body: Proposition, **kwargs
    ) -> Self | Implies[Proposition, UProposition] | UProposition:
        r"""
        Logical inference rule. Given self `(A /\ B /\ C...) -> D` is proven, and
        given one of the props (say B) in the antecedent is proven,
        return a proof of the new definite clause `(A /\ C /\ ...) -> D`
        or `A -> D` if only A is left in the body, or D if the antecedent is
        left empty.
        """
        return self.definite_clause_resolve([in_body], **kwargs)

    def first_unit_definite_clause_resolve(
        self, first_in_body: Proposition, **kwargs
    ) -> Self | Implies[Proposition, UProposition] | UProposition:
        r"""
        Logical inference rule. Given self `(A /\ B /\ C...) -> D` is proven, given A is proven,
        return a proof of the new definite clause `(B /\ C /\ ...) -> D`
        or D if the antecedent is left empty.
        Slightly faster than `unit_definite_clause_resolve`.
        """
        from pylogic.proposition.and_ import And

        dont_prove = kwargs.get("prove", True) is False
        if not dont_prove:
            assert self.is_proven, f"{self} is not proven"
        if not isinstance(self.antecedent, And):
            return first_in_body.modus_ponens(self, **kwargs)  # type: ignore
        if not dont_prove:
            assert first_in_body.is_proven, f"{first_in_body} is not proven"
        first_ante = self.antecedent.propositions[0]
        len_ante = len(self.antecedent.propositions)
        assert (
            first_in_body == first_ante
        ), f"{first_in_body} is not the first proposition {first_ante}"
        ante = self.antecedent.propositions[1] if len_ante == 2 else And(*self.antecedent.propositions[1:])  # type: ignore
        new_p = (
            Implies(
                ante,
                self.consequent,
                _is_proven=True,
                _assumptions=get_assumptions(self).union(
                    get_assumptions(first_in_body)
                ),
                _inference=Inference(
                    self, first_in_body, rule="first_unit_definite_clause_resolve"
                ),
            )
            if not dont_prove
            else Implies(ante, self.consequent)
        )
        return new_p  # type:ignore

    def unify(self, other: Self) -> Unification | Literal[True] | None:
        if not isinstance(other, Implies):
            raise TypeError(
                f"{other} is not an instance of {self.__class__}\n\
Occured when trying to unify `{self}` and `{other}`"
            )
        d: Unification = {}
        res1 = self.antecedent.unify(other.antecedent)
        if res1 is None:
            return None
        if isinstance(res1, dict):
            for k in res1:
                if k in d and d[k] != res1[k]:
                    return None
                d[k] = res1[k]
        res2 = self.consequent.unify(other.consequent)
        if res2 is None:
            return None
        if isinstance(res2, dict):
            for k in res2:
                if k in d and d[k] != res2[k]:
                    return None
                d[k] = res2[k]
        if len(d) == 0:
            return True
        else:
            return d

    def has_as_subproposition(self, other: Proposition) -> bool:
        """
        Check if other is a subproposition of self.
        """
        if self == other:
            return True
        _, first_other_occurs_in = find_first(
            lambda p: p.has_as_subproposition(other), [self.antecedent, self.consequent]
        )
        return first_other_occurs_in is not None

    def to_sympy(self) -> SpImplies:
        from sympy.logic.boolalg import Implies as SpImplies

        return SpImplies(self.antecedent.to_sympy(), self.consequent.to_sympy())
