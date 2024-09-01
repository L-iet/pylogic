from __future__ import annotations

from typing import TYPE_CHECKING, Any, Generic, Self, TypeVar

from pylogic.expressions.expr import Expr
from pylogic.helpers import replace
from pylogic.printing.printing import latex_print_order, str_print_order
from pylogic.proposition.proposition import get_assumptions
from pylogic.proposition.relation.relation import Relation

if TYPE_CHECKING:
    from fractions import Fraction

    from pylogic.structures.set_ import Set
    from pylogic.symbol import Symbol

    Numeric = Fraction | int | float
    PBasic = Symbol | Numeric
    Unevaluated = Symbol | Set | Expr
    Term = Unevaluated | Numeric
    C = TypeVar("C", bound="BinaryRelation")
else:
    Term = Any
T = TypeVar("T", bound=Term)
U = TypeVar("U", bound=Term)


class BinaryRelation(Relation, Generic[T, U]):
    is_transitive: bool = False  # forall a, b, c in S, a R b and b R c => a R c
    is_reflexive: bool = False  # forall a in S, a R a
    is_irreflexive: bool = False  # forall a in S, not a R a
    is_symmetric: bool = False  # forall a, b in S, a R b => b R a
    is_antisymmetric: bool = False  # forall a, b in S, a R b and b R a => a = b
    is_asymmetric: bool = False  # forall a, b in S, a R b => not b R a
    is_connected: bool = False  # forall a, b in S, a != b => a R b or b R a
    is_strongly_connected: bool = False  # forall a, b in S, a R b or b R a
    name: str = "BR"
    infix_symbol: str = "BR"
    infix_symbol_latex: str = "BR"

    def __init__(
        self,
        left: T,
        right: U,
        is_assumption: bool = False,
        description: str = "",
        **kwargs,
    ) -> None:
        super().__init__(
            self.name,
            args=[left, right],
            is_assumption=is_assumption,
            description=description,
            **kwargs,
        )
        self.left: T = left
        self.right: U = right

    def __repr__(self) -> str:
        return f"{str_print_order(self.left)} {self.infix_symbol} {str_print_order(self.right)}"

    def _latex(self, printer=None) -> str:
        left_latex = latex_print_order(self.left)
        right_latex = latex_print_order(self.right)
        return f"{left_latex} {self.infix_symbol_latex} {right_latex}"

    def copy(self) -> Self:
        # copy.copy and deepcopy are evaluating unevaluated expressions
        return self.__class__(
            self.left,
            self.right,
            description=self.description,
            is_assumption=self.is_assumption,
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
        """
        Replace current_val with new_val in the relation.
        """

        new_p = self.copy()

        if positions is None or [0] in positions:
            new_p.left = replace(new_p.left, current_val, new_val)
        if positions is None or [1] in positions:
            new_p.right = replace(new_p.right, current_val, new_val)
        return self.__class__(
            new_p.left,
            new_p.right,
            _is_proven=False,
        )

    def transitive(self, *others: Self) -> Self:
        """
        Logical Tactic. If self is of the form a Relation b and other is of the form b Relation c,
        returns a proven relation of the form a Relation c.
        Will try to evaluate expressions if self.right and other.left don't have
        the same structure.

        Raises NotImplementedError if the expression can't be evaluated and it is needed.
        """
        from pylogic.helpers import eval_same, find_first
        from pylogic.inference import Inference

        assert self.__class__.is_transitive, f"{self.__class__} is not transitive"
        assert self.is_proven, f"{self} is not proven"

        first_not_proven = find_first(lambda x: not x.is_proven, others)
        assert first_not_proven is None, f"{first_not_proven} is not proven"
        first_not_same_class = find_first(
            lambda x: x.__class__ != self.__class__, others
        )
        assert (
            first_not_same_class is None
        ), f"{first_not_same_class} is not a {self.__class__}"

        all_props = (self,) + others
        right_lefts = [(x.right, y.left) for x, y in zip(all_props[:-1], all_props[1:])]

        first_non_transitive = find_first(
            lambda x: not eval_same(x[0], x[1]), right_lefts
        )
        assert (
            first_non_transitive is None
        ), f"Chain of transitivity broken: {first_non_transitive} are not equal"

        new_p = self.__class__(
            self.left,
            others[-1].right,
            _is_proven=True,
            _assumptions=get_assumptions(self).union(
                *[get_assumptions(other) for other in others]
            ),
            _inference=Inference(self, *others, rule="transitive"),
        )
        return new_p

    def symmetric(self) -> BinaryRelation[U, T]:
        """
        Logical tactic. If self is proven, return a proof of self.right Relation self.left.
        """
        from pylogic.inference import Inference

        assert self.__class__.is_symmetric, f"{self.__class__} is not symmetric"
        assert self.is_proven, f"{self} is not proven"
        return self.__class__(
            self.right,  # type: ignore
            self.left,  # type: ignore
            _is_proven=True,
            _assumptions=get_assumptions(self),
            _inference=Inference(self, rule="symmetric"),
        )  # type: ignore

    @classmethod
    def reflexive(cls: type[C], term: T) -> C:
        """
        Logical tactic. Given a term, return a reflexive relation of the form term R term.
        """
        from pylogic.inference import Inference

        assert cls.is_reflexive, f"{cls} is not reflexive"
        return cls(
            term,
            term,
            _is_proven=True,
            _assumptions=set(),
            _inference=Inference(None, rule="reflexive"),
        )
