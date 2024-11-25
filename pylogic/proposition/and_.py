from __future__ import annotations

from typing import TYPE_CHECKING, Self, TypedDict, TypeVarTuple

from pylogic.inference import Inference
from pylogic.proposition._junction import _Junction
from pylogic.proposition.proposition import Proposition, get_assumptions

if TYPE_CHECKING:
    from sympy.logic.boolalg import And as SpAnd

    from pylogic.proposition.exor import ExOr
    from pylogic.proposition.implies import Implies
    from pylogic.proposition.not_ import Not
    from pylogic.proposition.or_ import Or

InferenceRule = TypedDict("InferenceRule", {"name": str, "arguments": list[str]})

Ps = TypeVarTuple("Ps")
Props = tuple[Proposition, ...]


class And(_Junction[*Ps]):
    # order of operations for propositions (0-indexed)
    # not xor and or => <=> forall forallInSet forallSubsets exists existsInSet existsUnique
    # existsUniqueInSet existsSubset existsUniqueSubset Proposition
    _precedence = 2

    _inference_rules: list[InferenceRule] = [
        {"name": "extract", "arguments": []},
        {"name": "all_proven", "arguments": []},
        {"name": "de_morgan", "arguments": []},
        {"name": "to_exor", "arguments": []},
        {"name": "left_distribute", "arguments": []},
        {"name": "right_distribute", "arguments": []},
        {"name": "distribute", "arguments": []},
    ]
    _distributes_over_ = {"Or", "ExOr"}

    def __init__(
        self,
        *propositions: *Ps,
        is_assumption: bool = False,
        description: str = "",
        **kwargs,
    ) -> None:
        super().__init__(
            "and",
            *propositions,
            is_assumption=is_assumption,
            description=description,
            **kwargs,
        )

    def __hash__(self) -> int:
        return super().__hash__()

    def __getitem__(self, index: int):
        """
        We get the proposition at the given index.
        Will prove that proposition if self is proven.
        """
        if self.is_proven:
            new_p = self.propositions[index]
            # have to bypass pylance to get Union[*Ps] to work
            if not TYPE_CHECKING:
                new_p = new_p.copy()
            new_p._set_is_proven(True)  # type: ignore
            new_p.deduced_from = Inference(new_p, self, rule="is_one_of")  # type: ignore
            new_p.from_assumptions = get_assumptions(self)  # type: ignore
            return new_p
        return self.propositions[index]  # type: ignore

    def __iter__(self):
        return iter(self.extract())

    def extract(self):
        """
        Logical inference rule. Get all conjunct of a conjunction as a tuple.

        Will prove all conjuncts if the conjunction is proven.
        """
        if self.is_proven:
            new_props: tuple[*Ps] = [p.copy() for p in self.propositions]  # type: ignore
            for p in new_props:
                p._set_is_proven(True)  # type: ignore
                p.deduced_from = Inference(p, self, rule="is_one_of")  # type: ignore
                p.from_assumptions = get_assumptions(self)  # type: ignore
            return new_props
        return self.propositions

    def remove_duplicates(self) -> And:
        return super().remove_duplicates()  # type: ignore

    def all_proven(self) -> Self:
        """Logical inference rule. If all propositions are proven, the conjunction is
        proven."""
        for p in self.propositions:
            if not p.is_proven:  # type: ignore
                raise ValueError(f"{p} is not proven")
        new_p = self.copy()
        new_p._set_is_proven(True)
        new_p.deduced_from = Inference(self, rule="all_proven")
        new_p.from_assumptions = get_assumptions(self).union(get_assumptions(p))  # type: ignore
        return new_p

    def de_morgan(self) -> Proposition:
        """Apply De Morgan's law to the conjunction to get an
        equivalent proposition.

        In intuitionistic logic, the only valid De Morgan's laws are

        `~A and ~B <-> ~(A or B)`

        `~A or ~B -> ~(A and B)`.

        In this case, the conjunction must be made of negations to return a different result..
        """
        # valid laws here
        # https://math.stackexchange.com/a/120209/1382176

        from pylogic.enviroment_settings.settings import settings
        from pylogic.proposition.not_ import Not, neg
        from pylogic.proposition.or_ import Or

        if settings["USE_CLASSICAL_LOGIC"] == False:
            if not all(isinstance(p, Not) for p in self.propositions):
                return self
            return Not(
                Or(*[p.negated.de_morgan() for p in self.propositions]),
                _is_proven=self.is_proven,
                _assumptions=get_assumptions(self),
                _inference=Inference(self, rule="de_morgan"),
            )

        negs: list[Proposition] = [
            neg(p.de_morgan()) for p in self.propositions  # type:ignore
        ]
        return Not(
            Or(*negs),  # type:ignore
            _is_proven=self.is_proven,
            _assumptions=get_assumptions(self),
            _inference=Inference(self, rule="de_morgan"),
        )

    def to_exor(self) -> ExOr[Proposition, ...]:  # type: ignore
        r"""
        Logical inference rule. If self is of the form
        `And(Or(A, B, C,...), A -> [~B /\ ~C /\...], B -> [~A /\ ~C /\...], C -> [~A /\ ~B /\...], ...)`,

        return `ExOr(A, B, C, ...)`.

        This can be slow if there are many propositions in the Or.

        Raises:
            AssertionError: If wrong structure of propositions is given.
            AttributeError: If the second, third, etc to the last proposition
            are not all implications with conjunctions as consequents.
        """
        from pylogic.helpers import find_first
        from pylogic.proposition.exor import ExOr
        from pylogic.proposition.not_ import neg

        assert isinstance(self.propositions[0], Or), "First proposition must be an Or"
        set_of_props: set[Proposition] = set(self.propositions[0].propositions)
        num_props = len(set_of_props)
        impls: tuple[Implies[Proposition, Proposition]] = self.propositions[1:]  # type: ignore
        antecedents = set(p.antecedent for p in impls)  # can raise AttributeError here
        assert (
            set_of_props == antecedents
        ), "Propositions in Or and implication antecedents not match"

        def get_props(p: Proposition) -> set[Proposition]:
            if num_props == 2:  # p is a negation
                return {neg(p)}
            # p is an And of negations
            assert isinstance(p, And), "p is not an And"
            return {neg(x) for x in p.propositions}

        def check_cons(impl: Implies[Proposition, Proposition]) -> bool:
            # check if there is mismatch in the consequent
            antecedent = impl.antecedent
            consequent = impl.consequent
            props = get_props(consequent)
            return props.union({antecedent}) != set_of_props

        ind, first_mismatch = find_first(check_cons, impls)
        assert (
            first_mismatch is None
        ), f"Consequent mismatch at index {ind+1} of propositions"
        return ExOr(
            *set_of_props,  # type: ignore
            description=self.description,
            is_assumption=self.is_assumption,
            _is_proven=self.is_proven,
            _assumptions=self.from_assumptions,
            _inference=Inference(self, rule="to_exor"),
        )

    def to_sympy(self) -> SpAnd:
        from sympy.logic.boolalg import And as SpAnd

        return SpAnd(*[p.to_sympy() for p in self.propositions])
