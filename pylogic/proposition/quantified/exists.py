from __future__ import annotations

from typing import TYPE_CHECKING, Callable, Self, TypedDict, TypeVar

from pylogic import Term
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
from pylogic.variable import Variable

TProposition = TypeVar("TProposition", bound="Proposition")
UProposition = TypeVar("UProposition", bound="Proposition")
B = TypeVar("B", bound="Proposition")

if TYPE_CHECKING:
    from pylogic.proposition.not_ import Not
    from pylogic.structures.set_ import Set
    from pylogic.symbol import Symbol


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
        variable = Variable(existential_var_name, latex_name=latex_name, **kwargs)
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

    def __eq__(self, other: Proposition) -> bool:
        if isinstance(other, Exists):
            return self.inner_proposition == other.inner_proposition
        return NotImplemented

    def __hash__(self) -> int:
        return super().__hash__()

    def __iter__(self):
        return iter(self.extract())

    def extract(self) -> tuple[Symbol, TProposition]:
        """Logical tactic.
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
            cls = Constant
        else:
            cls = Variable
        c = cls(
            self.variable.name,
            depends_on=other_free_vars,
            _from_existential_instance=True,
        )
        proven_inner = self.inner_proposition.replace({self.variable: c})
        proven_inner._set_is_proven(True)
        proven_inner.from_assumptions = get_assumptions(self).copy()
        proven_inner.deduced_from = Inference(self, rule="extract")
        if isinstance(proven_inner, And):
            c.knowledge_base.update(proven_inner.extract())
        else:
            c.knowledge_base.add(proven_inner)
        return (c, proven_inner)

    def exists_modus_ponens(self, other: Forall[Implies[TProposition, B]]) -> Exists[B]:
        """
        Logical tactic. If self is exists x: P(x) and given forall x: P(x) -> Q(x)
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

    def de_morgan(self) -> Not[Forall[Not[TProposition]]]:
        """
        Apply De Morgan's law to an existentially quantified sentence.
        """
        from pylogic.inference import Inference
        from pylogic.proposition.not_ import Not, neg
        from pylogic.proposition.quantified.forall import Forall

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


class ExistsInSet(Exists[And[IsContainedIn, TProposition]]):
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
        variable = Variable(existential_var_name, latex_name=latex_name, **kwargs)
        if expression_to_replace is not None:
            assert (
                expression_to_replace in set_
            ), f"{expression_to_replace} not in {set_}"
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

    def __hash__(self) -> int:
        return super().__hash__()

    def __repr__(self) -> str:
        return f"exists {self.variable} in {self.set_}: {self._inner_without_set}"

    def _latex(self, printer=None) -> str:
        var_latex = self.variable._latex()
        return rf"\exists {var_latex} \in {self.set_._latex()}: {self._inner_without_set._latex()}"

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

        if self.variable in replace_dict:
            raise ValueError("Cannot replace variable (not implemented)")
        if self.set_ in replace_dict:
            new_val = replace_dict[self.set_]
            assert isinstance(new_val, Set) or new_val.is_set, f"{new_val} is not a set"
            new_p = self.__class__(
                self.variable,
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
            self.variable,
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

    def __repr__(self) -> str:
        return f"exists 1 {self.variable}: {self._inner_without_unique}"

    def _latex(self, printer=None) -> str:
        var_latex = self.variable._latex()
        return rf"\exists ! {var_latex}: {self._inner_without_unique._latex()}"

    def replace(
        self,
        replace_dict: dict[Term, Term],
        positions: list[list[int]] | None = None,
        equal_check: Callable[[Term, Term], bool] | None = None,
    ) -> Self:
        if self.variable in replace_dict:
            raise ValueError("Cannot replace variable (not implemented)")

        new_p = self.__class__(
            self.variable,
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

    def _latex(self, printer=None) -> str:
        var_latex = self.variable._latex()
        return rf"\exists ! {var_latex} \in {self.set_._latex()}: {self._inner_without_set_and_unique._latex()}"

    def replace(
        self,
        replace_dict: dict[Term, Term],
        positions: list[list[int]] | None = None,
        equal_check: Callable[[Term, Term], bool] | None = None,
    ) -> Self:
        from pylogic.structures.set_ import Set

        if self.variable in replace_dict:
            raise ValueError("Cannot replace variable (not implemented)")
        if self.set_ in replace_dict:
            new_val = replace_dict[self.set_]
            assert isinstance(new_val, Set), f"{new_val} is not a set"
            new_p = self.__class__(
                self.variable,
                new_val,
                self._inner_without_set_and_unique.replace(
                    replace_dict, positions=positions, equal_check=equal_check
                ),
                _is_proven=False,
            )
            return new_p

        new_p = self.__class__(
            self.variable,
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

    def __hash__(self) -> int:
        return super().__hash__()

    def __repr__(self) -> str:
        return (
            f"exists {self.variable} subset of {self.set_}: {self._inner_without_set}"
        )

    def _latex(self, printer=None) -> str:
        var_latex = self.variable._latex()
        return rf"\exists {var_latex} \subseteq {self.set_._latex()}: {self._inner_without_set._latex()}"

    to_exists = ExistsInSet.to_exists
    replace = ExistsInSet.replace
    copy = ExistsInSet.copy
    deepcopy = ExistsInSet.deepcopy


class ExistsUniqueSubset(
    ExistsSubset[And[TProposition, Forall[Implies[TProposition, Equals]]]]
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
        return f"exists 1 {self.variable} subset of {self.set_}: {self._inner_without_set_and_unique}"

    def _latex(self, printer=None) -> str:
        var_latex = self.variable._latex()
        return rf"\exists ! {var_latex} \subseteq {self.set_._latex()}: {self._inner_without_set_and_unique._latex()}"

    replace = ExistsUniqueInSet.replace
    copy = ExistsUniqueInSet.copy
    deepcopy = ExistsUniqueInSet.deepcopy
