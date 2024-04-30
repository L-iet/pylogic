from __future__ import annotations
from pylogic.proposition.proposition import Proposition, get_assumptions
from pylogic.proposition.quantified.quantified import _Quantified
from pylogic.variable import Variable
from typing import TYPE_CHECKING, TypedDict, TypeVar, Self

if TYPE_CHECKING:
    from sympy import Basic
    from pylogic.proposition.quantified.forall import Forall
    from pylogic.proposition.not_ import Not
    from pylogic.proposition.implies import Implies
    from pylogic.symbol import Symbol
    from pylogic.structures.sets import Set

    Term = Symbol | Set | Basic | int | float

TProposition = TypeVar("TProposition", bound="Proposition")
UProposition = TypeVar("UProposition", bound="Proposition")
B = TypeVar("B", bound="Proposition")
Tactic = TypedDict("Tactic", {"name": str, "arguments": list[str]})


class Exists(_Quantified[TProposition]):
    tactics: list[Tactic] = [
        {"name": "exists_modus_ponens", "arguments": ["Forall"]},
        {"name": "de_morgan", "arguments": []},
    ]

    @classmethod
    def from_proposition(
        cls,
        existential_var_name: str,
        expression_to_replace: Term | None,
        inner_proposition: TProposition,
        positions: list[list[int]] | None = None,
        is_assumption: bool = False,
        is_real: bool = True,
        description: str = "",
        **kwargs,
    ) -> Exists[TProposition]:
        r"""
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
        variable = Variable(existential_var_name, real=is_real)
        if expression_to_replace is not None:
            inner_proposition = inner_proposition.replace(
                expression_to_replace, variable, positions=positions
            )
        return cls(
            variable,
            inner_proposition,
            is_assumption,
            description=description,
            **kwargs,
        )

    def __init__(
        self,
        variable: Variable,
        inner_proposition: TProposition,
        is_assumption: bool = False,
        description: str = "",
        **kwargs,
    ) -> None:
        super().__init__(
            "exists",
            variable,
            inner_proposition,
            is_assumption,
            description=description,
            **kwargs,
        )

    def __eq__(self, other: Proposition) -> bool:
        if isinstance(other, Exists):
            return self.inner_proposition == other.inner_proposition
        return False

    def __hash__(self) -> int:
        return super().__hash__()

    def __iter__(self):
        return iter((self.variable, self.inner_proposition))

    def copy(self) -> Self:
        return self.__class__(
            self.variable,
            self.inner_proposition.copy(),
            self.is_assumption,
            description=self.description,
            _is_proven=self.is_proven,
            _assumptions=self.from_assumptions,
            _inference=self.deduced_from,
        )

    def exists_modus_ponens(self, other: Forall[Implies[TProposition, B]]) -> Exists[B]:
        """
        Logical tactic. If self is exists x: P(x) and given forall x: P(x) -> Q(x)
        and each is proven, conclude exists x: Q(x).
        """
        from pylogic.proposition.quantified.forall import Forall
        from pylogic.inference import Inference

        assert self.is_proven, f"{self} is not proven"
        assert isinstance(other, Forall), f"{other} is not a forall statement"
        assert other.is_proven, f"{other} is not proven"
        assert self.inner_proposition == other.inner_proposition.antecedent

        other_cons = other.inner_proposition.consequent.copy()
        new_p = Exists(
            variable=other.variable,
            inner_proposition=other_cons,  # type: ignore
            is_assumption=False,
            _is_proven=True,
            _assumptions=get_assumptions(self).union(get_assumptions(other)),
            _inference=Inference(self, other, rule="exists_modus_ponens"),
        )
        return new_p

    def de_morgan(self) -> Not[Forall[Not[TProposition]]]:
        """
        Apply De Morgan's law to an existentially quantified sentence.
        """
        from pylogic.proposition.not_ import Not, neg
        from pylogic.proposition.quantified.forall import Forall
        from pylogic.inference import Inference

        inner_negated = neg(self.inner_proposition.de_morgan())
        return Not(
            Forall(self.variable, inner_negated),
            _is_proven=self.is_proven,
            _assumptions=get_assumptions(self).copy(),
            _inference=Inference(self, rule="de_morgan"),
        )
