from __future__ import annotations

from typing import TYPE_CHECKING, Callable, Self, TypedDict, TypeVar

from pylogic.constant import Constant
from pylogic.inference import Inference
from pylogic.proposition.and_ import And
from pylogic.proposition.implies import Implies
from pylogic.proposition.proposition import Proposition, get_assumptions
from pylogic.proposition.quantified.forall import Forall
from pylogic.proposition.quantified.quantified import _Quantified
from pylogic.proposition.relation.contains import IsContainedIn
from pylogic.proposition.relation.equals import Equals
from pylogic.proposition.relation.subsets import IsSubsetOf
from pylogic.typing import Term
from pylogic.variable import Variable

TProposition = TypeVar("TProposition", bound="Proposition")
UProposition = TypeVar("UProposition", bound="Proposition")
B = TypeVar("B", bound="Proposition")

if TYPE_CHECKING:
    from pylogic.proposition.not_ import Not
    from pylogic.structures.set_ import Set
    from pylogic.symbol import Symbol


InferenceRule = TypedDict("InferenceRule", {"name": str, "arguments": list[str]})


class Exists(_Quantified[TProposition]):
    # order of operations for propositions (0-indexed)
    # not xor and or => <=> forall forallInSet forallSubsets exists existsInSet existsUnique
    # existsUniqueInSet existsSubset existsUniqueSubset Proposition
    _precedence = 9

    _inference_rules: list[InferenceRule] = [
        {"name": "exists_modus_ponens", "arguments": ["Forall"]},
        {"name": "extract", "arguments": []},
        {"name": "de_morgan", "arguments": []},
        {"name": "to_exists_in_set", "arguments": []},
        {"name": "to_exists_unique", "arguments": []},
        {"name": "to_exists_unique_in_set", "arguments": []},
    ]

    _q = "exists"
    _bin_symb = None
    _innermost_prop_attr = "inner_proposition"

    @classmethod
    def from_proposition(
        cls,
        existential_var_name: str,
        expression_to_replace: Term | None,
        inner_proposition: TProposition,
        latex_name: str | None = None,
        positions: list[list[int]] | None = None,
        is_assumption: bool = False,
        description: str = "",
        **kwargs,
    ) -> Exists[TProposition]:
        r"""
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

        Other keyword arguments are passed to the variable.
        """
        context = kwargs.pop("context", None)
        variable = Variable(
            existential_var_name, latex_name=latex_name, context=context, **kwargs
        )
        if expression_to_replace is not None:
            inner_proposition = inner_proposition.replace(
                {expression_to_replace: variable},
                positions=positions,
                equal_check=kwargs.get("equal_check"),
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

        # And or Proposition or None
        self._non_inner_prop: Proposition | None = None

    def __eq__(self, other: Proposition) -> bool:
        if isinstance(other, Exists):
            return self.inner_proposition == other.inner_proposition
        return NotImplemented

    def __hash__(self) -> int:
        return super().__hash__()

    def __iter__(self):
        return iter(self.extract())

    def extract(
        self, name: str | None = None, latex_name: str | None = None
    ) -> tuple[Symbol, TProposition]:
        """Logical inference rule.
        If self is proven, return a constant and a proven inner proposition.
        """
        assert self.is_proven, f"{self} is not proven"
        from pylogic.proposition.and_ import And

        other_free_vars = tuple(
            {
                v
                for v in self.inner_proposition.variables
                if (not v.is_bound) and (v != self.variable)
            }
        )
        if not other_free_vars:
            if self.variable.is_set:
                from pylogic.structures.set_ import Set

                cls = Set
            elif self.variable.is_sequence:
                from pylogic.structures.sequence import Sequence

                cls = Sequence
            else:
                cls = Constant
        else:
            cls = Variable
        c = cls(
            name or self.variable.name,
            latex_name=latex_name or name or self.variable.latex_name,
            depends_on=other_free_vars,
            _from_existential_instance=True,
            set_=self.variable.is_set,
            sequence=self.variable.is_sequence,
            length=getattr(self.variable, "length", None),
        )
        proven_inner = self.inner_proposition.replace({self.variable: c})
        proven_inner._set_is_proven(True)
        proven_inner.from_assumptions = get_assumptions(self).copy()
        proven_inner.deduced_from = Inference(
            self, conclusion=proven_inner, rule="extract"
        )
        if isinstance(proven_inner, And):
            c.knowledge_base.update(proven_inner.extract())
        else:
            c.knowledge_base.add(proven_inner)
        return (c, proven_inner)

    def exists_modus_ponens(self, other: Forall[Implies[TProposition, B]]) -> Exists[B]:
        """
        Logical inference rule. If self is exists x: P(x) and given forall x: P(x) -> Q(x)
        and each is proven, conclude exists x: Q(x).
        """
        from pylogic.inference import Inference
        from pylogic.proposition.quantified.forall import Forall

        assert self.is_proven, f"{self} is not proven"
        assert isinstance(other, Forall), f"{other} is not a forall statement"
        assert other.is_proven, f"{other} is not proven"
        assert self.inner_proposition == other.inner_proposition.antecedent

        other_cons = other.inner_proposition.consequent
        new_p = Exists(
            variable=other.variable,
            inner_proposition=other_cons,  # type: ignore
            is_assumption=False,
            _is_proven=True,
            _assumptions=get_assumptions(self).union(get_assumptions(other)),
            _inference=Inference(self, other, rule="exists_modus_ponens"),
        )
        return new_p

    def de_morgan(self) -> Proposition:
        """
        Apply De Morgan's law to an existentially quantified sentence.

        In intuitionistic logic, the only valid De Morgan's laws are

        `~A and ~B <-> ~(A or B)`

        `~A or ~B -> ~(A and B)`.
        """
        from pylogic.enviroment_settings.settings import settings
        from pylogic.inference import Inference
        from pylogic.proposition.not_ import Not, neg
        from pylogic.proposition.quantified.forall import Forall

        if settings["USE_CLASSICAL_LOGIC"] == False:
            if not isinstance(self.inner_proposition, Not):
                return self
            self.variable.unbind()
            return Not(
                Forall(self.variable, self.inner_proposition.negated.de_morgan()),
                _is_proven=self.is_proven,
                _assumptions=get_assumptions(self).copy(),
                _inference=Inference(self, rule="de_morgan"),
            )

        inner_negated = neg(self.inner_proposition.de_morgan())
        self.variable.unbind()
        return Not(
            Forall(self.variable, inner_negated),
            _is_proven=self.is_proven,
            _assumptions=get_assumptions(self).copy(),
            _inference=Inference(self, rule="de_morgan"),
        )

    def to_exists_in_set(self, **kwargs) -> ExistsInSet[Proposition]:
        """
        If self matches the structure,

        exists x: (x in set /\\ P (x))

        convert self to an `ExistsInSet` statement.
        """
        inner_prop = self.inner_proposition
        match inner_prop:
            case And(propositions=[IsContainedIn(left=self.variable), *props]):
                return ExistsInSet(
                    variable=self.variable,
                    set_=inner_prop.propositions[0].set_,
                    inner_proposition=And(*props) if len(props) > 1 else props[0],  # type: ignore
                    is_assumption=self.is_assumption,
                    description=self.description,
                    _is_proven=self._is_proven,
                    _assumptions=self.from_assumptions,
                    _inference=self.deduced_from,
                    **kwargs,
                )
        raise ValueError(f"Cannot convert {self} to ExistsInSet")

    def to_exists_unique(self, **kwargs) -> ExistsUnique[Proposition]:
        """
        If self matches the structure,

        exists x: (P (x) /\\ forall y: [P (y) -> y = x])

        convert self to an `ExistsUnique` statement.
        """
        inner_prop = self.inner_proposition
        match inner_prop:
            case And(
                propositions=[
                    new_inner,
                    Forall(
                        variable=y1,
                        inner_proposition=Implies(
                            antecedent=implies_antecedent,
                            consequent=Equals(left=y2, right=self.variable),
                        ),
                    ),
                ]
            ) if (y1 == y2) and (
                implies_antecedent == new_inner.replace({self.variable: y1})
            ):
                return ExistsUnique(
                    variable=self.variable,
                    inner_proposition=new_inner,
                    is_assumption=self.is_assumption,
                    description=self.description,
                    _is_proven=self._is_proven,
                    _assumptions=self.from_assumptions,
                    _inference=self.deduced_from,
                    **kwargs,
                )
        raise ValueError(f"Cannot convert {self} to ExistsUnique")

    def to_exists_unique_in_set(self, **kwargs) -> ExistsUniqueInSet[Proposition]:
        """
        If self matches the structure,

        exists x: x in set /\\ P (x) /\\ [forall y: (y in set /\\ P (y)) -> y = x])

        convert self to an `ExistsUniqueInSet` statement.
        """
        inner_prop = self.inner_proposition
        match inner_prop:
            case And(
                propositions=[
                    IsContainedIn(left=self.variable, right=set_1),
                    *Pxs,
                    Forall(
                        variable=y1,
                        inner_proposition=Implies(
                            antecedent=And(
                                propositions=[IsContainedIn(left=y2, right=set_2), *Pys]
                            ),
                            consequent=Equals(left=y3, right=self.variable),
                        ),
                    ),
                ]
            ) if (
                (y1 == y2 == y3)
                and (set_1 == set_2)
                and all(
                    Px.replace({self.variable: y1}) == Py for Px, Py in zip(Pxs, Pys)
                )
            ):
                return ExistsUniqueInSet(
                    variable=self.variable,
                    set_=set_1,
                    inner_proposition=Pxs[0] if len(Pxs) == 1 else And(*Pxs),  # type: ignore
                    is_assumption=self.is_assumption,
                    description=self.description,
                    _is_proven=self._is_proven,
                    _assumptions=self.from_assumptions,
                    _inference=self.deduced_from,
                    **kwargs,
                )  # type: ignore
        raise ValueError(f"Cannot convert {self} to ExistsUniqueInSet")

    def by_single_substitution(
        self, term: Term, proven_proposition: Proposition | None = None
    ) -> Self:
        """
        Logical inference rule.
        If self is `exists x: P(x)` and term is `y` and `P(y)` is proven,
        return a proven `exists x: P(x)`.
        """
        from pylogic.proposition.and_ import And

        if proven_proposition is not None:
            assert proven_proposition.is_proven, f"{proven_proposition} is not proven"

        inner_replaced = self.inner_proposition.replace({self.variable: term})
        if proven_proposition is not None and inner_replaced == proven_proposition:
            new_prop = self.copy()
            new_prop._set_is_proven(True)
            new_prop.from_assumptions = get_assumptions(proven_proposition)
            new_prop.deduced_from = Inference(
                proven_proposition, conclusion=new_prop, rule="by_substitution"
            )
            return new_prop

        kb = term.knowledge_base
        if proven_proposition is not None:
            kb = kb.union({proven_proposition})

        if isinstance(inner_replaced, And):
            for prop in inner_replaced.propositions:
                if (not prop.by_inspection_check()) and prop not in kb:
                    raise ValueError(
                        f"{self} cannot be proven by substitution:\n{prop} is not true by inspection or in the knowledge base"
                    )
        new_prop = self.copy()
        new_prop._set_is_proven(True)

        # TODO: fix this to use the assumptions from the KB
        new_prop.from_assumptions = (
            get_assumptions(proven_proposition) if proven_proposition else set()
        )
        new_prop.deduced_from = Inference(
            *term.knowledge_base, conclusion=new_prop, rule="by_single_substitution"
        )
        return new_prop
        # replace inner_prop with term.
        # if result equals proven, return new prop
        # else if result is conjunction, new kb = term kb + {proven}
        # for each prop in conjunction, if prop true by inspection
        # or prop in kb, cross it off
        # if all crossed off, return new prop
        # else raise error

    def by_substitution(self, *terms: Term, proven: Proposition) -> Self:
        """
        Logical inference rule.
        Continually substitute until the innermost exists proposition is unwrapped.

        If self is `exists x: exists y: P(x, y)` and terms is `(a, b)` and `P(a, b)` is proven,
        return a proven `exists x: exists y: P(x, y)`.
        """
        assert proven.is_proven, f"{proven} is not proven"
        first_non_exists = getattr(self, self._innermost_prop_attr)
        innermost_exists = self
        i = 0
        variables = {innermost_exists.variable: terms[i]}
        while isinstance(first_non_exists, Exists):
            non_inner_proven = innermost_exists._prove_non_inner(terms[i])
            if not non_inner_proven:
                raise ValueError(
                    f"{self} cannot be proven by substitution:\n{innermost_exists} is not true by inspection or in the knowledge base"
                )
            innermost_exists = first_non_exists

            first_non_exists = getattr(
                innermost_exists, innermost_exists._innermost_prop_attr
            )
            i += 1
            variables[innermost_exists.variable] = terms[i]
        non_inner_proven = innermost_exists._prove_non_inner(terms[i])
        if not non_inner_proven:
            raise ValueError(
                f"{self} cannot be proven by substitution:\n{innermost_exists} is not true by inspection or in the knowledge base"
            )
        if (first_non_exists_replaced := first_non_exists.replace(variables)) == proven:
            new_prop = self.copy()
            new_prop._set_is_proven(True)
            new_prop.from_assumptions = get_assumptions(proven)
            new_prop.deduced_from = Inference(
                proven, conclusion=new_prop, rule="by_substitution"
            )
            return new_prop
        raise ValueError(
            f"{self} cannot be proven by substitution:\n{first_non_exists_replaced} is not equal to {proven}"
        )

    def _prove_non_inner(self, term: Term) -> bool:
        """
        Given a term, return True if we can prove the non-inner parts of the existential
        proposition, and False otherwise.

        For an ExistsInSet proposition, return True if we can prove `term in self.set_`.

        For an ExistsUnique proposition, return True if we can prove `term is unique`.

        For an ExistsSubset proposition, return True if we can prove `term issubset self.set_`.

        etc.
        """
        from pylogic.proposition.and_ import And

        if self._non_inner_prop is None:
            return True

        proven = False
        if isinstance(self._non_inner_prop, And):
            replaced = [
                prop.replace({self.variable: term})
                for prop in self._non_inner_prop.propositions
            ]
            proven = all(
                [
                    rep in term.knowledge_base or replaced.by_inspection_check()
                    for rep in replaced
                ]
            )
        elif proven is False and isinstance(self._non_inner_prop, Proposition):
            replaced = self._non_inner_prop.replace({self.variable: term})
            proven = replaced in term.knowledge_base or replaced.by_inspection_check()
        return proven


class ExistsInSet(Exists[And[IsContainedIn, TProposition]]):
    # order of operations for propositions (0-indexed)
    # not xor and or => <=> forall forallInSet forallSubsets exists existsInSet existsUnique
    # existsUniqueInSet existsSubset existsUniqueSubset Proposition
    _precedence = 10

    _q = "exists"
    _bin_symb = "in"
    _innermost_prop_attr = "_inner_without_set"

    @classmethod
    def from_proposition(
        cls,
        existential_var_name: str,
        expression_to_replace: Term | None,
        set_: Set | Variable,
        inner_proposition: TProposition,
        latex_name: str | None = None,
        positions: list[list[int]] | None = None,
        is_assumption: bool = False,
        description: str = "",
        **kwargs,
    ) -> ExistsInSet[TProposition]:
        r"""
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
        Other keyword arguments are passed to the variable.
        """
        context = kwargs.pop("context", None)
        variable = Variable(
            existential_var_name, latex_name=latex_name, context=context, **kwargs
        )
        if expression_to_replace is not None:
            assert expression_to_replace.is_in(
                set_
            ).by_inspection_check(), f"{expression_to_replace} not in {set_}"
            inner_proposition = inner_proposition.replace(
                {expression_to_replace: variable},
                positions=positions,
                equal_check=kwargs.get("equal_check"),
            )
        return cls(
            variable,
            set_,
            inner_proposition,
            is_assumption=is_assumption,
            description=description,
            **kwargs,
        )

    def __init__(
        self,
        variable: Variable,
        set_: Set | Variable,
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
        self._non_inner_prop = IsContainedIn(self.variable, set_)

    def __hash__(self) -> int:
        return super().__hash__()

    def to_exists(self, **kwargs) -> Exists[And[IsContainedIn, TProposition]]:
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
            **kwargs,
        )

    def to_exists_in_set(self, **kwargs) -> Self:
        return self

    def replace(
        self,
        replace_dict: dict[Term, Term],
        positions: list[list[int]] | None = None,
        equal_check: Callable[[Term, Term], bool] | None = None,
    ) -> Self:
        from pylogic.structures.set_ import Set

        new_var = self.variable
        if self.variable in replace_dict:
            assert isinstance(
                replace_dict[self.variable], Variable
            ), "Cannot replace variable with non-variable"
            new_var = replace_dict[self.variable]
        if self.set_ in replace_dict:
            new_val = replace_dict[self.set_]
            assert isinstance(new_val, Set) or new_val.is_set, f"{new_val} is not a set"
            new_p = self.__class__(
                new_var,
                new_val,
                self._inner_without_set.replace(
                    replace_dict,
                    positions=positions,
                    equal_check=equal_check,
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


class ExistsUnique(Exists[And[TProposition, Forall[Implies[TProposition, Equals]]]]):
    # order of operations for propositions (0-indexed)
    # not xor and or => <=> forall forallInSet forallSubsets exists existsInSet existsUnique
    # existsUniqueInSet existsSubset existsUniqueSubset Proposition
    _precedence = 11

    _q = "exists 1"
    _bin_symb = None
    _innermost_prop_attr = "_inner_without_unique"

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

        prev_latex_name = variable.latex_name.split("_")
        if len(prev_latex_name) > 1:
            # assuming curly braces are opened and closed correctly
            if prev_latex_name[1].startswith("{"):
                subscript = prev_latex_name[1][1:-1]
            else:
                subscript = prev_latex_name[1]
            under_2 = r"\_2"
            prev_latex_name[1] = f"{{{subscript + under_2}}}"
        else:
            prev_latex_name.append(r"\_2")
        new_latex_name = "_".join(prev_latex_name)
        other_var = Variable(variable.name + "_2", latex_name=new_latex_name)
        other_prop = inner_proposition.replace({variable: other_var})
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
        self._non_inner_prop = Forall(
            other_var, Implies(other_prop, Equals(other_var, self.variable))
        )

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
            self._inner_without_unique.replace(
                replace_dict, positions=positions, equal_check=equal_check
            ),
            _is_proven=False,
        )
        return new_p

    def to_exists_unique(self, **kwargs) -> Self:
        return self

    def copy(self) -> Self:
        return self.__class__(
            self.variable,
            self._inner_without_unique,
            is_assumption=self.is_assumption,
            description=self.description,
            _is_proven=self._is_proven,
            _assumptions=self.from_assumptions,
            _inference=self.deduced_from,
        )

    def deepcopy(self) -> Self:
        return self.__class__(
            self.variable.deepcopy(),
            self._inner_without_unique.deepcopy(),
            is_assumption=self.is_assumption,
            description=self.description,
            _is_proven=self._is_proven,
            _assumptions=self.from_assumptions,
            _inference=self.deduced_from,
        )


class ExistsUniqueInSet(
    ExistsInSet[And[TProposition, Forall[Implies[TProposition, Equals]]]]
):
    # order of operations for propositions (0-indexed)
    # not xor and or => <=> forall forallInSet forallSubsets exists existsInSet existsUnique
    # existsUniqueInSet existsSubset existsUniqueSubset Proposition
    _precedence = 12

    _q = "exists 1"
    _bin_symb = "in"
    _innermost_prop_attr = "_inner_without_set_and_unique"

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

        prev_latex_name = variable.latex_name.split("_")
        if len(prev_latex_name) > 1:
            # assuming curly braces are opened and closed correctly
            if prev_latex_name[1].startswith("{"):
                subscript = prev_latex_name[1][1:-1]
            else:
                subscript = prev_latex_name[1]
            under_2 = r"\_2"
            prev_latex_name[1] = f"{{{subscript + under_2}}}"
        else:
            prev_latex_name.append(r"\_2")
        new_latex_name = "_".join(prev_latex_name)
        other_var = Variable(variable.name + "_2", latex_name=new_latex_name)
        other_prop = inner_proposition.replace({variable: other_var})
        super().__init__(
            variable,
            set_,
            IsContainedIn(variable, set_).and_(
                inner_proposition,
                ForallInSet(
                    other_var, set_, other_prop.implies(Equals(other_var, variable))
                ),
            ),
            is_assumption=is_assumption,
            description=description,
            **kwargs,
        )
        self._inner_without_set_and_unique = inner_proposition
        self._non_inner_prop = IsContainedIn(self.variable, set_).and_(
            ForallInSet(
                other_var, set_, other_prop.implies(Equals(other_var, self.variable))
            )
        )

    def replace(
        self,
        replace_dict: dict[Term, Term],
        positions: list[list[int]] | None = None,
        equal_check: Callable[[Term, Term], bool] | None = None,
    ) -> Self:
        from pylogic.structures.set_ import Set

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
                self._inner_without_set_and_unique.replace(
                    replace_dict, positions=positions, equal_check=equal_check
                ),
                _is_proven=False,
            )
            return new_p

        new_p = self.__class__(
            new_var,
            self.set_,
            self._inner_without_set_and_unique.replace(
                replace_dict, positions=positions, equal_check=equal_check
            ),
            _is_proven=False,
        )
        return new_p

    def to_exists_unique_in_set(self, **kwargs) -> Self:
        return self

    def copy(self) -> Self:
        return self.__class__(
            self.variable,
            self.set_,
            self._inner_without_set_and_unique,
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
            self._inner_without_set_and_unique.deepcopy(),
            is_assumption=self.is_assumption,
            description=self.description,
            _is_proven=self._is_proven,
            _assumptions=self.from_assumptions,
            _inference=self.deduced_from,
        )


class ExistsSubset(Exists[And[IsSubsetOf, TProposition]]):
    # order of operations for propositions (0-indexed)
    # not xor and or => <=> forall forallInSet forallSubsets exists existsInSet existsUnique
    # existsUniqueInSet existsSubset existsUniqueSubset Proposition
    _precedence = 13

    _q = "exists"
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
            IsSubsetOf(variable, set_).and_(inner_proposition),
            is_assumption=is_assumption,
            description=description,
            **kwargs,
        )
        self.set_ = set_
        self.right_set = set_
        self._inner_without_set = inner_proposition
        self._non_inner_prop = IsSubsetOf(self.variable, set_)

    def __hash__(self) -> int:
        return super().__hash__()

    to_exists = ExistsInSet.to_exists
    replace = ExistsInSet.replace
    copy = ExistsInSet.copy
    deepcopy = ExistsInSet.deepcopy


class ExistsUniqueSubset(
    ExistsSubset[And[TProposition, Forall[Implies[TProposition, Equals]]]]
):
    # order of operations for propositions (0-indexed)
    # not xor and or => <=> forall forallInSet forallSubsets exists existsInSet existsUnique
    # existsUniqueInSet existsSubset existsUniqueSubset Proposition
    _precedence = 14

    _q = "exists 1"
    _bin_symb = "subset of"
    _innermost_prop_attr = "_inner_without_set_and_unique"

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

        prev_latex_name = variable.latex_name.split("_")
        if len(prev_latex_name) > 1:
            # assuming curly braces are opened and closed correctly
            if prev_latex_name[1].startswith("{"):
                subscript = prev_latex_name[1][1:-1]
            else:
                subscript = prev_latex_name[1]
            under_2 = r"\_2"
            prev_latex_name[1] = f"{{{subscript + under_2}}}"
        else:
            prev_latex_name.append(r"\_2")
        new_latex_name = "_".join(prev_latex_name)
        other_var = Variable(variable.name + "_2", latex_name=new_latex_name)
        other_prop = inner_proposition.replace({variable: other_var})
        super().__init__(
            variable,
            set_,
            IsSubsetOf(variable, set_).and_(
                inner_proposition,
                ForallInSet(
                    other_var, set_, other_prop.implies(Equals(other_var, variable))
                ),
            ),
            is_assumption=is_assumption,
            description=description,
            **kwargs,
        )
        self._inner_without_set_and_unique = inner_proposition
        self._non_inner_prop = IsSubsetOf(self.variable, set_).and_(
            ForallInSet(
                other_var, set_, other_prop.implies(Equals(other_var, self.variable))
            )
        )

    replace = ExistsUniqueInSet.replace
    copy = ExistsUniqueInSet.copy
    deepcopy = ExistsUniqueInSet.deepcopy
