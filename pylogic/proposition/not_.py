from __future__ import annotations

from typing import (
    TYPE_CHECKING,
    Callable,
    Generic,
    Literal,
    Self,
    TypedDict,
    TypeVar,
    overload,
)

from pylogic import Term, Unification
from pylogic.enviroment_settings.settings import settings
from pylogic.proposition.proposition import Proposition, get_assumptions

if TYPE_CHECKING:
    from sympy.logic.boolalg import Not as SpNot

    from pylogic.proposition.implies import Implies
    from pylogic.proposition.relation.binaryrelation import BinaryRelation

    T = TypeVar("T", bound=BinaryRelation)
else:
    T = TypeVar("T")

TProposition = TypeVar("TProposition", bound="Proposition")
UProposition = TypeVar("UProposition", bound="Proposition")
InferenceRule = TypedDict("InferenceRule", {"name": str, "arguments": list[str]})


@overload
def neg(
    p: Not[TProposition], is_assumption: bool = False, **kwargs
) -> TProposition: ...
@overload
def neg(
    p: TProposition, is_assumption: bool = False, **kwargs
) -> Not[TProposition]: ...
def neg(
    p: Not[TProposition] | TProposition, is_assumption: bool = False, **kwargs
) -> Not[TProposition] | TProposition:
    """
    Given a proposition, return its negation.
    In intuitionistic logic, double-negation-elimination is not valid, so
    the result of neg(Not(p)) is ~~p.

    In classical logic, double-negation-elimination is valid, so the result of
    neg(Not(p)) is p.
    Keyword arguments are not used in this case for neg(Not(p)): the result is p.
    """
    if isinstance(p, Not) and settings["USE_CLASSICAL_LOGIC"]:
        return p.negated
    return Not(p, is_assumption, **kwargs)


def are_negs(p: Proposition, q: Proposition) -> bool:
    """Given two propositions, determine if they are negations
    of each other.
    """
    if isinstance(p, Not):
        return p.negated == q
    elif isinstance(q, Not):
        return q.negated == p
    return False


class Not(Proposition, Generic[TProposition]):
    # order of operations for propositions (0-indexed)
    # not xor and or => <=> forall forallInSet forallSubsets exists existsInSet existsUnique
    # existsUniqueInSet existsSubset existsUniqueSubset Proposition
    _precedence = 0

    _inference_rules: list[InferenceRule] = [
        {"name": "modus_tollens", "arguments": ["Implies"]},
        {"name": "de_morgan", "arguments": []},
        {"name": "symmetric", "arguments": []},
    ]

    def __init__(
        self,
        negated: TProposition,
        is_assumption: bool = False,
        description: str = "",
        **kwargs,
    ) -> None:
        self.negated: TProposition = negated
        name = rf"~{negated}"
        super().__init__(name, is_assumption, description=description, **kwargs)
        self.is_atomic = False
        self.bound_vars = negated.bound_vars.copy()
        self.variables = negated.variables.copy()
        self.constants = negated.constants.copy()
        self.sets = negated.sets.copy()
        self.class_ns = negated.class_ns.copy()
        self._set_init_inferred_attrs()

    def __str__(self) -> str:
        from pylogic.proposition.quantified.quantified import _Quantified

        # only wrap the innermost proposition in parentheses if it is not atomic
        # and not a quantified proposition
        inner_part = (
            f"({self.negated})"
            if (not self.negated.is_atomic)
            and (not isinstance(self.negated, (_Quantified, Not)))
            else str(self.negated)
        )
        return f"~{inner_part}"

    def _latex(self, printer=None) -> str:
        from pylogic.proposition.quantified.quantified import _Quantified
        from pylogic.proposition.relation.binaryrelation import BinaryRelation
        from pylogic.proposition.relation.divides import Divides

        if isinstance(self.negated, Divides):
            p = self.negated
            if (
                p.quotient_set.name == "Integers"
                and p.quotient_set.__class__.__name__ == "IntegersRing"
            ):
                return rf"\left. {p.a._latex()} \nmid {p.b._latex()} \right."
            return rf"\frac{{{p.b._latex()}}}{{{p.a._latex()}}} \not\in {p.quotient_set._latex()}"
        elif isinstance(self.negated, BinaryRelation):
            p = self.negated
            return rf"{p.left._latex()} \not {p.infix_symbol_latex} {p.right._latex()}"

        # only wrap the innermost proposition in parentheses if it is not atomic
        # and not a quantified proposition
        inner_part = (
            rf"\left({self.negated._latex()}\right)"
            if (not self.negated.is_atomic)
            and (not isinstance(self.negated, (_Quantified, Not)))
            else self.negated._latex()
        )
        return rf"\neg {inner_part}"

    def __repr__(self) -> str:
        return f"Not({self.negated!r})"

    def __eq__(self, other: Proposition) -> bool:
        if isinstance(other, Not):
            return other.negated == self.negated
        return NotImplemented

    def __hash__(self) -> int:
        return hash(("not", self.negated))

    def _set_is_inferred(self, value: bool) -> None:
        super()._set_is_inferred(value)
        from pylogic.constant import Constant
        from pylogic.proposition.relation.binaryrelation import BinaryRelation
        from pylogic.proposition.relation.equals import Equals
        from pylogic.structures.set_ import EmptySet

        match self.negated:
            case Equals(right=r):
                if r == EmptySet:
                    if value:
                        self.negated.left.is_empty = False
                        self.negated.left.knowledge_base.add(self)
                    else:
                        self.negated.left.is_empty = None
                        self.negated.left.knowledge_base.discard(self)
                elif r == Constant(0):
                    if value:
                        self.negated.left.is_zero = False
                        self.negated.left.knowledge_base.add(self)
                    else:
                        self.negated.left.is_zero = None
                        self.negated.left.knowledge_base.discard(self)
            case BinaryRelation():
                if value:
                    self.negated.left.knowledge_base.add(self)
                else:
                    self.negated.left.knowledge_base.discard(self)

    def _set_is_proven(self, value: bool) -> None:
        super()._set_is_proven(value)
        if (not value) and not (self.is_axiom or self.is_assumption):
            self._set_is_inferred(False)

    def _set_is_assumption(self, value: bool, **kwargs) -> None:
        super()._set_is_assumption(value, **kwargs)
        if (not value) and not (self._is_proven or self.is_axiom):
            self._set_is_inferred(False)

    def _set_is_axiom(self, value: bool) -> None:
        super()._set_is_axiom(value)
        if (not value) and not (self._is_proven or self.is_assumption):
            self._set_is_inferred(False)

    def copy(self) -> Self:
        return self.__class__(
            self.negated,
            is_assumption=self.is_assumption,
            description=self.description,
            _is_proven=self._is_proven,
            _assumptions=self.from_assumptions,
            _inference=self.deduced_from,
        )

    def deepcopy(self) -> Self:
        return self.__class__(
            self.negated.deepcopy(),
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
            + "it is false that\n"
            + self.negated.as_text(_indent=_indent + 1)
        )

    def describe(self, *, _indent=0) -> str:
        """
        Return a description of the proposition.
        """
        if self.description:
            return "  " * _indent + self.description + "\n"
        return (
            "  " * _indent
            + "it is false that\n"
            + self.negated.describe(_indent=_indent + 1)
        )

    def replace(
        self,
        replace_dict: dict[Term, Term],
        positions: list[list[int]] | None = None,
        equal_check: Callable[[Term, Term], bool] | None = None,
    ) -> Self:
        new_p = self.__class__(
            self.negated.replace(
                replace_dict, positions=positions, equal_check=equal_check
            )
        )
        return new_p

    @overload
    def modus_tollens(
        self,
        other: Implies[Not[UProposition], TProposition],
    ) -> UProposition: ...

    @overload
    def modus_tollens(
        self,
        other: Implies[UProposition, TProposition],
    ) -> Not[UProposition]: ...

    def modus_tollens(
        self,
        other: (
            Implies[Not[UProposition], TProposition]
            | Implies[UProposition, TProposition]
        ),
    ) -> UProposition | Not[UProposition]:
        """
        Logical inference rule.
        other: Implies
            Must be an implication that has been proven whose structure is
            OtherProposition -> ~self
        """
        return super().modus_tollens(other)  # type: ignore

    def de_morgan(self) -> Proposition:
        """
        Apply De Morgan's law to this negation.

        In intuitionistic logic, the only valid De Morgan's laws are

        `~A and ~B <-> ~(A or B)`

        `~A or ~B -> ~(A and B)`.
        """
        from pylogic.inference import Inference
        from pylogic.proposition.and_ import And
        from pylogic.proposition.or_ import Or

        if isinstance(self.negated, And):
            if settings["USE_CLASSICAL_LOGIC"] == False:
                return self
            negs: list[Proposition] = [
                neg(p.de_morgan()) for p in self.negated.propositions  # type:ignore
            ]
            return Or(
                *negs,  # type: ignore
                _is_proven=self.is_proven,
                _assumptions=get_assumptions(self).copy(),
                _inference=Inference(self, rule="de_morgan"),
            )
        elif isinstance(self.negated, Or):
            if settings["USE_CLASSICAL_LOGIC"] == False:
                negs = [Not(p.de_morgan()) for p in self.negated.propositions]
            else:
                negs: list[Proposition] = [
                    neg(p.de_morgan()) for p in self.negated.propositions  # type:ignore
                ]
            return And(
                *negs,  # type: ignore
                _is_proven=self.is_proven,
                _assumptions=get_assumptions(self).copy(),
                _inference=Inference(self, rule="de_morgan"),
            )
        elif self.negated.is_atomic:
            return self

        return neg(
            self.negated.de_morgan(),
            _is_proven=self.is_proven,
            _assumptions=get_assumptions(self).copy(),
            _inference=Inference(self, rule="de_morgan"),
        )

    def unify(self, other: Self) -> Unification | Literal[True] | None:
        if not isinstance(other, Not):
            raise TypeError(
                f"{other} is not an instance of {self.__class__}\n\
Occured when trying to unify `{self}` and `{other}`"
            )
        return self.negated.unify(other.negated)

    def has_as_subproposition(self, other: Proposition) -> bool:
        """
        Check if other is a subproposition of self.
        """
        if self == other:
            return True
        return self.negated.has_as_subproposition(other)

    def symmetric(self: Not[T]) -> Not[BinaryRelation]:
        """
        Logical inference rule. If self is ~(a R b), where R is a symmetric relation,
        return a proof of ~(b R a).
        """
        from pylogic.inference import Inference

        cls = self.negated.__class__
        assert cls.is_symmetric, f"{cls} is not symmetric"
        return Not(
            self.negated.symmetric(),
            _is_proven=self.is_proven,
            _assumptions=get_assumptions(self),
            _inference=Inference(self, rule="symmetric"),
        )

    def by_inspection_check(self) -> bool | None:
        """
        Check if self is provable by inspection.
        Returns True if self.negated.by_inspection() returns False,
        False if self.negated.by_inspection() returns True, and None if neither is provable.
        """
        from pylogic.helpers import ternary_not

        return ternary_not(self.negated.by_inspection_check())

    def to_sympy(self) -> SpNot:
        from sympy.logic.boolalg import Not as SpNot

        return SpNot(self.negated.to_sympy())
