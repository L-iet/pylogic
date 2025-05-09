from __future__ import annotations

from typing import Callable, Generic, Self, TypeVar

from pylogic.helpers import replace
from pylogic.proposition.proposition import get_assumptions
from pylogic.proposition.relation.relation import Relation
from pylogic.typing import Term

C = TypeVar("C", bound="BinaryRelation")
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
    infix_symbol_latex: str = "BR "

    def __init__(
        self,
        left: T,
        right: U,
        name: str = "BR",
        is_assumption: bool = False,
        description: str = "",
        **kwargs,
    ) -> None:
        super().__init__(
            name,
            args=[left, right],
            is_assumption=is_assumption,
            description=description,
            **kwargs,
        )
        self.left: T = self.args[0]
        self.right: U = self.args[1]

        self._set_init_inferred_attrs()

    def __repr__(self) -> str:
        return f"{self.__class__.__name__}({self.left}, {self.right})"

    def __str__(self) -> str:
        from pylogic.enviroment_settings.settings import settings

        if settings["SHOW_ALL_PARENTHESES"]:
            wrap = lambda p: f"({p})" if not p.is_atomic else str(p)
        else:
            wrap = lambda p: str(p)
        return f"{wrap(self.left)} {self.infix_symbol} {wrap(self.right)}"

    def _latex(self, printer=None) -> str:
        from pylogic.enviroment_settings.settings import settings

        if settings["SHOW_ALL_PARENTHESES"]:
            wrap = lambda p: (
                rf"\left({p._latex()}\right)" if not p.is_atomic else p._latex()
            )
        else:
            wrap = lambda p: p._latex()
        return f"{wrap(self.left)} {self.infix_symbol_latex} {wrap(self.right)}"

    def _set_is_inferred(self, value: bool) -> None:
        super()._set_is_inferred(value)
        if value:
            self.left.knowledge_base.add(self)
        else:
            self.left.knowledge_base.discard(self)

    def _set_is_proven(self, value: bool, **kwargs) -> None:
        super()._set_is_proven(value, **kwargs)
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
            self.left,
            self.right,
            name=self.name,
            description=self.description,
            is_assumption=self.is_assumption,
            _is_proven=self._is_proven,
            _assumptions=self.from_assumptions,
            _inference=self.deduced_from,
        )

    def evaluate(self, **kwargs) -> Self:
        """
        Evaluate the Relation.
        """
        from pylogic.inference import Inference

        return self.__class__(
            self.left.evaluate(),
            self.right.evaluate(),
            _is_proven=self.is_proven,
            _assumptions=get_assumptions(self) if self.is_proven else set(),
            _inference=Inference(self, rule="evaluate") if self.is_proven else None,
        )

    def deepcopy(self) -> Self:
        from pylogic.helpers import deepcopy

        return self.__class__(
            deepcopy(self.left),
            deepcopy(self.right),
            name=self.name,
            description=self.description,
            is_assumption=self.is_assumption,
            _is_proven=self._is_proven,
            _assumptions=self.from_assumptions,
            _inference=self.deduced_from,
        )

    def replace(
        self,
        replace_dict: dict[Term, Term],
        positions: list[list[int]] | None = None,
        equal_check: Callable[[Term, Term], bool] | None = None,
    ) -> Self:
        """
        Replace current_val with new_val in the relation.
        """
        # don't use copy/deepcopy here; can result in recursion error
        # when used with propositions containing set structures as their `property`s
        # reference the sets themselves
        new_left = old_left = self.left
        new_right = old_right = self.right

        if positions is None or [0] in positions:
            new_left = replace(
                old_left, replace_dict, equal_check=equal_check, positions=positions
            )
        if positions is None or [1] in positions:
            new_right = replace(
                old_right, replace_dict, equal_check=equal_check, positions=positions
            )
        return self.__class__(
            new_left,
            new_right,
            name=self.name,
            _is_proven=False,
        )

    def transitive(self, *others: Self) -> Self:
        """
        Logical InferenceRule. If self is of the form a ~ b and other is of the form b ~ c, or of the form (b ~ c or b = c),
        returns a proven relation of the form a ~ c.
        Will try to evaluate expressions if self.right and other.left don't have
        the same structure.

        Raises NotImplementedError if the expression can't be evaluated and it is needed.
        """
        from pylogic.helpers import eval_same, find_first
        from pylogic.inference import Inference

        assert self.__class__.is_transitive, f"{self.__class__} is not transitive"
        assert self.is_proven, f"{self} is not proven"

        _, first_not_proven = find_first(lambda x: not x.is_proven, others)
        assert first_not_proven is None, f"{first_not_proven} is not proven"
        _, first_not_same_class = find_first(
            lambda x: x.__class__ != self.__class__, others
        )
        assert (
            first_not_same_class is None
        ), f"{first_not_same_class} is not a {self.__class__}"

        all_props = (self,) + others
        right_lefts = [(x.right, y.left) for x, y in zip(all_props[:-1], all_props[1:])]

        _, first_non_transitive = find_first(
            lambda x: not eval_same(x[0], x[1]), right_lefts
        )
        assert (
            first_non_transitive is None
        ), f"Chain of transitivity broken: {first_non_transitive[0]} and {first_non_transitive[1]} are not identical"

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
        Logical inference rule. If self is proven, return a proof of self.right Relation self.left.
        """
        from pylogic.inference import Inference

        assert self.__class__.is_symmetric, f"{self.__class__} is not symmetric"
        return self.__class__(
            self.right,  # type: ignore
            self.left,  # type: ignore
            _is_proven=self.is_proven,
            _assumptions=get_assumptions(self),
            _inference=Inference(self, rule="symmetric"),
        )  # type: ignore

    @classmethod
    def reflexive(cls: type[C], term: T) -> C:
        """
        Logical inference rule. Given a term, return a reflexive relation of the form term R term.
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

    def by_inspection_check(self) -> bool | None:
        return True if self in self.left.knowledge_base else None
