from __future__ import annotations
from pylogic.proposition.proposition import Proposition, get_assumptions
from pylogic.proposition.and_ import And
from pylogic.proposition.relation.contains import IsContainedIn
from pylogic.proposition.quantified.quantified import _Quantified
from pylogic.proposition.quantified.forall import Forall
from pylogic.proposition.implies import Implies
from pylogic.proposition.relation.equals import Equals
from pylogic.variable import Variable
from pylogic.constant import Constant
from pylogic.inference import Inference
from typing import TYPE_CHECKING, TypedDict, TypeVar, Self

TProposition = TypeVar("TProposition", bound="Proposition")
UProposition = TypeVar("UProposition", bound="Proposition")
B = TypeVar("B", bound="Proposition")

if TYPE_CHECKING:
    from fractions import Fraction
    from pylogic.expressions.expr import Expr
    from pylogic.proposition.not_ import Not
    from pylogic.symbol import Symbol
    from pylogic.structures.set_ import Set
    from sympy import Basic

    Numeric = Fraction | int | float
    PBasic = Symbol | Numeric
    Unevaluated = Symbol | Set | Expr
    Term = Unevaluated | Numeric | Basic


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
        return iter(self.extract())

    def extract(self) -> tuple[Constant, TProposition]:
        """Logical tactic.
        If self is proven, return a constant and a proven inner proposition.
        """
        assert self.is_proven, f"{self} is not proven"

        c = Constant(f"c_{self.variable.name}")
        proven_inner = self.inner_proposition.replace(self.variable, c)
        proven_inner._is_proven = True
        proven_inner.from_assumptions = get_assumptions(self).copy()
        proven_inner.deduced_from = Inference(self, rule="extract")
        return (c, proven_inner)

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
        self.variable.unbind()
        return Not(
            Forall(self.variable, inner_negated),
            _is_proven=self.is_proven,
            _assumptions=get_assumptions(self).copy(),
            _inference=Inference(self, rule="de_morgan"),
        )


class ExistsInSet(Exists[And[IsContainedIn, TProposition]]):
    def __init__(
        self,
        variable: Variable,
        set_: Set,
        inner_proposition: TProposition,
        is_assumption: bool = False,
        description: str = "",
        **kwargs,
    ) -> None:
        super().__init__(
            variable,
            IsContainedIn(variable, set_).and_(inner_proposition),
            is_assumption=is_assumption,
            description=description,
            **kwargs,
        )
        self.set_ = set_
        self._inner_without_set = inner_proposition

    def __hash__(self) -> int:
        return super().__hash__()

    def __repr__(self) -> str:
        return f"exists {self.variable} in {self.set_}: {self._inner_without_set}"

    def to_exists(self) -> Exists[And[IsContainedIn, TProposition]]:
        """
        Convert self to a regular `exists` statement.
        """
        return Exists(
            self.variable,
            self.inner_proposition,
            is_assumption=self.is_assumption,
            description=self.description,
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
        if current_val == self.variable:
            raise ValueError("Cannot replace variable (not implemented)")
        if current_val == self.set_:
            assert isinstance(new_val, Set), f"{new_val} is not a set"
            new_p = self.__class__(
                self.variable,
                new_val,
                self._inner_without_set.replace(
                    current_val, new_val, positions=positions
                ),
                _is_proven=False,
            )

        new_p = self.__class__(
            self.variable,
            self.set_,
            self._inner_without_set.replace(current_val, new_val, positions=positions),
            _is_proven=False,
        )
        return new_p


class ExistsUnique(Exists[And[TProposition, Forall[Implies[TProposition, Equals]]]]):
    def __init__(
        self,
        variable: Variable,
        inner_proposition: TProposition,
        is_assumption: bool = False,
        description: str = "",
        **kwargs,
    ) -> None:
        from pylogic.proposition.quantified.forall import Forall
        from pylogic.proposition.relation.equals import Equals

        other_var = Variable(variable.name + "_2")
        other_prop = inner_proposition.replace(variable, other_var)
        super().__init__(
            variable,
            inner_proposition.and_(
                Forall(other_var, Implies(other_prop, Equals(other_var, variable)))
            ),
            is_assumption=is_assumption,
            description=description,
            **kwargs,
        )
        self._inner_without_unique = inner_proposition

    def __repr__(self) -> str:
        return f"exists 1 {self.variable}: {self._inner_without_unique}"

    def replace(
        self,
        current_val: Term,
        new_val: Term,
        positions: list[list[int]] | None = None,
    ) -> Self:
        if current_val == self.variable:
            raise ValueError("Cannot replace variable (not implemented)")

        new_p = self.__class__(
            self.variable,
            self._inner_without_unique.replace(
                current_val, new_val, positions=positions
            ),
            _is_proven=False,
        )
        return new_p


class ExistsUniqueInSet(
    ExistsInSet[And[TProposition, Forall[Implies[TProposition, Equals]]]]
):
    def __init__(
        self,
        variable: Variable,
        set_: Set,
        inner_proposition: TProposition,
        is_assumption: bool = False,
        description: str = "",
        **kwargs,
    ) -> None:
        from pylogic.proposition.quantified.forall import ForallInSet

        other_var = Variable(variable.name + "_2")
        other_prop = inner_proposition.replace(variable, other_var)
        super().__init__(
            variable,
            set_,
            inner_proposition.and_(
                ForallInSet(
                    other_var, set_, other_prop.implies(Equals(other_var, variable))
                )
            ),
            is_assumption=is_assumption,
            description=description,
            **kwargs,
        )
        self._inner_without_set_and_unique = inner_proposition

    def __repr__(self) -> str:
        return f"exists 1 {self.variable} in {self.set_}: {self._inner_without_set_and_unique}"

    def replace(
        self,
        current_val: Term,
        new_val: Term,
        positions: list[list[int]] | None = None,
    ) -> Self:
        if current_val == self.variable:
            raise ValueError("Cannot replace variable (not implemented)")
        if current_val == self.set_:
            assert isinstance(new_val, Set), f"{new_val} is not a set"
            new_p = self.__class__(
                self.variable,
                new_val,
                self._inner_without_set_and_unique.replace(
                    current_val, new_val, positions=positions
                ),
                _is_proven=False,
            )

        new_p = self.__class__(
            self.variable,
            self.set_,
            self._inner_without_set_and_unique.replace(
                current_val, new_val, positions=positions
            ),
            _is_proven=False,
        )
        return new_p
