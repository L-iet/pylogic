from __future__ import annotations

from typing import TYPE_CHECKING, Any, Callable, Self, TypedDict, TypeVar

import sympy as sp

from pylogic.inference import Inference
from pylogic.proposition.implies import Implies
from pylogic.proposition.proposition import Proposition, get_assumptions
from pylogic.proposition.quantified.quantified import _Quantified
from pylogic.proposition.relation.contains import IsContainedIn
from pylogic.proposition.relation.subsets import IsSubsetOf
from pylogic.typing import Term

if TYPE_CHECKING:
    from pylogic.proposition.not_ import Not
    from pylogic.proposition.quantified.exists import Exists
    from pylogic.proposition.relation.equals import Equals
    from pylogic.structures.sequence import Sequence
    from pylogic.structures.set_ import Set
    from pylogic.variable import Variable

TProposition = TypeVar("TProposition", bound="Proposition")
UProposition = TypeVar("UProposition", bound="Proposition")
B = TypeVar("B", bound="Proposition")
InferenceRule = TypedDict("InferenceRule", {"name": str, "arguments": list[str]})


class Forall(_Quantified[TProposition]):
    # order of operations for propositions (0-indexed)
    # not xor and or => <=> forall forallInSet forallSubsets exists existsInSet existsUnique
    # existsUniqueInSet existsSubset existsUniqueSubset Proposition
    _precedence = 6

    _inference_rules: list[InferenceRule] = [
        {"name": "quantified_modus_ponens", "arguments": ["Implies"]},
        {"name": "in_particular", "arguments": ["Term"]},
        {"name": "de_morgan", "arguments": []},
    ]

    _q = "forall"
    _bin_symb = None
    _innermost_prop_attr = "inner_proposition"

    def __init__(
        self,
        variable: Variable,
        inner_proposition: TProposition,
        is_assumption: bool = False,
        description: str = "",
        **kwargs,
    ) -> None:
        super().__init__(
            "forall",
            variable,
            inner_proposition,
            is_assumption,
            description=description,
            **kwargs,
        )

    def __call__(self, *terms: Term) -> Proposition:
        prop = self
        i = 0
        while isinstance(prop, Forall) and i < len(terms):
            prop = prop.in_particular(terms[i])
            i += 1
        return prop

    def __eq__(self, other: Proposition) -> bool:
        if isinstance(other, Forall):
            return self.inner_proposition == other.inner_proposition
        return NotImplemented

    def __hash__(self) -> int:
        return super().__hash__()

    def extract_conjuncts(self) -> list[Proposition]:
        """
        Logical inference rule. Given self is proven and is of the form
        `forall x: P(x) and Q(x)`, (or `forall x in S: P(x) and Q(x)`, etc),
        return the propositions
        [`forall x: P(x)`, `forall x: Q(x)`] (or [`forall x in S: P(x)`, `forall x in S: Q(x)`]).
        """
        from pylogic.proposition.and_ import And

        assert self.is_proven, f"{self} is not proven"
        innermost_prop = getattr(self, self._innermost_prop_attr)
        assert isinstance(innermost_prop, And), f"{innermost_prop} is not an `And`"
        conjuncts = innermost_prop.propositions
        return [
            self.__class__(
                self.variable,
                set_=getattr(self, "set_", None),
                inner_proposition=conj,
                _is_proven=True,
                _assumptions=get_assumptions(self),
                _inference=Inference(self, rule="extract_conjuncts"),
            )
            for conj in conjuncts
        ]

    def forall_modus_ponens(
        self, other: Forall[Implies[TProposition, B]] | Exists[Implies[TProposition, B]]
    ) -> Forall[B] | Exists[B]:
        """
        Logical inference rule. If self is forall x: P(x) and given P(x) -> Q(x) or forall x: P(x) -> Q(x)
        (or exists x: P(x) -> Q(x)), and each is proven, conclude
        forall x: Q(x) (or exists x: Q(x)).
        """
        from pylogic.proposition.quantified.exists import Exists

        quant_class = other.__class__
        assert (
            quant_class == Forall or quant_class == Exists or quant_class == Implies
        ), f"{other} is must be `Forall`, `Exists` or `Implies`"
        if quant_class == Implies:
            impl: Implies = other
        else:
            assert isinstance(
                other.inner_proposition, Implies
            ), f"{other.inner_proposition} is not an implication"
            impl = other.inner_proposition
        assert self.is_proven, f"{self} is not proven"
        assert other.is_proven, f"{other} is not proven"
        assert self.inner_proposition == impl.antecedent

        other_cons = impl.consequent
        new_p: Forall[B] | Exists[B] = quant_class(
            variable=other.variable,
            inner_proposition=other_cons,  # type: ignore
            is_assumption=False,
            _is_proven=True,
            _assumptions=get_assumptions(self).union(get_assumptions(other)),
            _inference=Inference(self, other, rule="forall_modus_ponens"),
        )
        return new_p

    def replace(
        self,
        replace_dict: dict[Term, Term],
        positions: list[list[int]] | None = None,
        equal_check: Callable[[Term, Term], bool] | None = None,
    ) -> Self:
        new_var = self.variable
        if self.variable in replace_dict:
            assert isinstance(
                replace_dict[self.variable], Variable
            ), "Cannot replace variable with non-variable"
            new_var = replace_dict[self.variable]
        new_p = self.__class__(
            new_var,
            self.inner_proposition.replace(
                replace_dict, positions=positions, equal_check=equal_check
            ),
            _is_proven=False,
        )
        return new_p

    def in_particular(self, expression_to_substitute: Term, **kwargs) -> TProposition:
        """Logical inference rule. Given self is proven, replace the variable in the inner
        proposition and get a proven proposition.
        """
        from pylogic.helpers import python_to_pylogic
        from pylogic.variable import Variable

        dont_prove = kwargs.get("prove", True) is False

        expression_to_substitute = python_to_pylogic(expression_to_substitute)

        # TODO: may need to define or override .replace for Forall to prevent
        # unnecessarily replacing the variable in the inner proposition

        if not dont_prove:
            assert self.is_proven, f"{self} is not proven"

        if isinstance(expression_to_substitute, Variable):
            expression_to_substitute.unbind()
    
        new_p = self.inner_proposition.replace(
            {self.variable: expression_to_substitute}
        )
        if not dont_prove:
            new_p._set_is_proven(True)
            new_p.from_assumptions = get_assumptions(self).copy()
            new_p.deduced_from = Inference(self, rule="in_particular")
        return new_p

    def de_morgan(self) -> Proposition:
        """
        Apply De Morgan's law to a universally quantified sentence.

        In intuitionistic logic, the only valid De Morgan's laws are

        `~A and ~B <-> ~(A or B)`

        `~A or ~B -> ~(A and B)`.
        """
        from pylogic.enviroment_settings.settings import settings
        from pylogic.proposition.not_ import Not, neg
        from pylogic.proposition.quantified.exists import Exists

        if settings["USE_CLASSICAL_LOGIC"] == False:
            if not isinstance(self.inner_proposition, Not):
                return self
            self.variable.unbind()
            return Not(
                Exists(self.variable, self.inner_proposition.negated.de_morgan()),
                _is_proven=self.is_proven,
                _assumptions=get_assumptions(self).copy(),
                _inference=Inference(self, rule="de_morgan"),
            )

        inner_negated = neg(self.inner_proposition.de_morgan())
        self.variable.unbind()
        return Not(
            Exists(self.variable, inner_negated),
            _is_proven=self.is_proven,
            _assumptions=get_assumptions(self).copy(),
            _inference=Inference(self, rule="de_morgan"),
        )


class ForallInSet(Forall[Implies[IsContainedIn, TProposition]]):
    # order of operations for propositions (0-indexed)
    # not xor and or => <=> forall forallInSet forallSubsets exists existsInSet existsUnique
    # existsUniqueInSet existsSubset existsUniqueSubset Proposition
    _precedence = 7

    _q = "forall"
    _bin_symb = "in"
    _innermost_prop_attr = "_inner_without_set"

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
            IsContainedIn(variable, set_).implies(inner_proposition),
            is_assumption,
            description=description,
            **kwargs,
        )
        self.set_ = set_
        self._inner_without_set = inner_proposition

    def __hash__(self) -> int:
        return super().__hash__()

    def replace(
        self,
        replace_dict: dict[Term, Term],
        positions: list[list[int]] | None = None,
        equal_check: Callable[[Term, Term], bool] | None = None,
    ) -> Self:
        from pylogic.structures.set_ import Set
        from pylogic.variable import Variable

        new_var = self.variable
        if self.variable in replace_dict:
            assert isinstance(
                replace_dict[self.variable], Variable
            ), "Cannot replace variable with non-variable"
            new_var = replace_dict[self.variable]
        if self.set_ in replace_dict:
            new_val = replace_dict[self.set_]
            assert isinstance(new_val, Set), f"{new_val} is not a set"
            new_p = self.__class__(
                new_var,
                new_val,
                self._inner_without_set.replace(
                    replace_dict, positions=positions, equal_check=equal_check
                ),
                _is_proven=False,
            )
            return new_p

        new_p = self.__class__(
            new_var,
            self.set_,
            self._inner_without_set.replace(
                replace_dict, positions=positions, equal_check=equal_check
            ),
            _is_proven=False,
        )
        return new_p

    def copy(self) -> Self:
        return self.__class__(
            self.variable,
            self.set_,
            self._inner_without_set,
            is_assumption=self.is_assumption,
            description=self.description,
            _is_proven=self._is_proven,
            _assumptions=self.from_assumptions,
            _inference=self.deduced_from,
        )

    def deepcopy(self) -> Self:
        return self.__class__(
            self.variable.deepcopy(),
            self.set_.deepcopy(),
            self._inner_without_set.deepcopy(),
            is_assumption=self.is_assumption,
            description=self.description,
            _is_proven=self._is_proven,
            _assumptions=self.from_assumptions,
            _inference=self.deduced_from,
        )

    def to_forall(self) -> Forall[Implies[IsContainedIn, TProposition]]:
        """
        Convert self to a regular `forall` statement.
        """
        return Forall(
            self.variable,
            self.inner_proposition,
            is_assumption=self.is_assumption,
            description=self.description,
            _is_proven=self._is_proven,
            _assumptions=self.from_assumptions,
            _inference=self.deduced_from,
        )

    def neq_any_thus_not_in_set(self) -> Not[IsContainedIn]:
        """
        Logical inference rule. Given self is proven, where self is of the form
        `forall x in S: A != x`, return a proof of `~(A in S)`.
        """
        assert self.is_proven, f"{self} is not proven"
        from pylogic.proposition.not_ import Not
        from pylogic.proposition.relation.contains import IsContainedIn
        from pylogic.proposition.relation.equals import Equals

        match self._inner_without_set:
            case Not(negated=Equals(left=a, right=b)) if b == self.variable:
                new_p = Not(
                    IsContainedIn(a, self.set_),
                    _is_proven=True,
                    _assumptions=get_assumptions(self),
                    _inference=Inference(self, rule="neq_any_thus_not_in_set"),
                )
                return new_p
        raise ValueError(f"{self} is not of the form `forall x in S: A != x`")

    def neq_any_thus_not_in_sequence(self) -> Not[IsContainedIn]:
        """
        Logical inference rule. Given self is proven, where self is of the form
        `forall k in Naturals: A != s[k]`, return a proof of `~(A in {s_n})`.
        """
        assert self.is_proven, f"{self} is not proven"
        from pylogic.expressions.sequence_term import SequenceTerm
        from pylogic.proposition.not_ import Not
        from pylogic.proposition.relation.contains import IsContainedIn
        from pylogic.proposition.relation.equals import Equals
        from pylogic.structures.set_ import SeqSet

        if not (
            self.set_.name == "Naturals"
            and self.set_.__class__.__name__ == "NaturalsSemiring"
        ):
            raise ValueError(
                f"{self} is not of the form `forall k in Naturals: A != s[k]`"
            )
        match self._inner_without_set:
            case Not(
                negated=Equals(left=a, right=SequenceTerm(sequence=s, index=ind))
            ) if ind == self.variable:
                new_p = Not(
                    IsContainedIn(a, SeqSet(s)),
                    _is_proven=True,
                    _assumptions=get_assumptions(self),
                    _inference=Inference(self, rule="neq_any_thus_not_in_sequence"),
                )
                return new_p
        raise ValueError(f"{self} is not of the form `forall k in Naturals: A != s[k]`")

    def in_particular(
        self,
        expression_to_substitute: Term,
        proof_expr_to_substitute_in_set: Proposition | None = None,
        **kwargs
    ) -> TProposition:
        """Logical inference rule. Given self is proven, replace the variable in the inner
        proposition and get a proven proposition.
        """
        dont_prove = kwargs.get("prove", True) is False
        if not dont_prove:
            assert self.is_proven, f"{self} is not proven"
        impl = super().in_particular(expression_to_substitute, **kwargs)
        if proof_expr_to_substitute_in_set is None:
            try:
                # this is fine even with prove=False because ValueError
                # will be raised if there is no proof it is in the set
                # so impl will be returned
                # otherwise, it will return the inner implication at the end
                ante = IsContainedIn(
                    expression_to_substitute, self.set_
                ).by_inspection()
            except ValueError:
                return impl
        elif (
            self.set_.predicate is not None
            and proof_expr_to_substitute_in_set
            == self.set_.predicate(expression_to_substitute)
        ):
            ante = IsContainedIn(expression_to_substitute, self.set_).by_predicate(
                proof_expr_to_substitute_in_set, **kwargs
            )
        elif isinstance(proof_expr_to_substitute_in_set, IsContainedIn):
            ante = proof_expr_to_substitute_in_set
        else:
            return impl
        new_p = impl.first_unit_definite_clause_resolve(ante, **kwargs)
        return new_p  # type: ignore


class ForallSubsets(Forall[Implies[IsSubsetOf, TProposition]]):
    # order of operations for propositions (0-indexed)
    # not xor and or => <=> forall forallInSet forallSubsets exists existsInSet existsUnique
    # existsUniqueInSet existsSubset existsUniqueSubset Proposition
    _precedence = 8

    _q = "forall"
    _bin_symb = "subset of"
    _innermost_prop_attr = "_inner_without_set"

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
            IsSubsetOf(variable, set_).implies(inner_proposition),
            is_assumption=is_assumption,
            description=description,
            **kwargs,
        )
        self.right_set = set_
        self.set_ = set_
        self._inner_without_set = inner_proposition

    replace = ForallInSet.replace
    copy = ForallInSet.copy
    deepcopy = ForallInSet.deepcopy
    to_forall = ForallInSet.to_forall

    def in_particular(
        self,
        expression_to_substitute: Term,
        proof_expr_to_substitute_is_subset: IsSubsetOf | None = None,
        **kwargs
    ) -> TProposition:
        """Logical inference rule. Given self is proven, replace the variable in the inner
        proposition and get a proven proposition.
        """
        dont_prove = kwargs.get("prove", True) is False
        if not dont_prove:
            assert self.is_proven, f"{self} is not proven"
        impl = super().in_particular(expression_to_substitute, **kwargs)
        if proof_expr_to_substitute_is_subset is None:
            try:
                # see ForallInSet.in_particular for explanation
                ante = IsSubsetOf(
                    expression_to_substitute, self.right_set
                ).by_inspection()
            except ValueError:
                return impl
        else:
            ante = proof_expr_to_substitute_is_subset
        new_p = impl.first_unit_definite_clause_resolve(ante, **kwargs)
        return new_p  # type: ignore
