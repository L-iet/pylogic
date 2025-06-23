from __future__ import annotations

import warnings
from typing import (
    TYPE_CHECKING,
    Callable,
    Literal,
    Self,
    TypedDict,
    TypeVar,
    TypeVarTuple,
    cast,
    overload,
)

from pylogic.enviroment_settings.settings import settings
from pylogic.helpers import fn_alias

if TYPE_CHECKING:
    from pylogic.constant import Constant
    from pylogic.helpers import Side
    from pylogic.proposition.and_ import And
    from pylogic.proposition.contradiction import Contradiction
    from pylogic.proposition.exor import ExOr
    from pylogic.proposition.iff import Iff
    from pylogic.proposition.implies import Implies
    from pylogic.proposition.not_ import Not
    from pylogic.proposition.or_ import Or
    from pylogic.proposition.quantified.exists import Exists, ExistsInSet
    from pylogic.proposition.quantified.forall import Forall, ForallInSet
    from pylogic.proposition.relation.contains import IsContainedIn
    from pylogic.proposition.relation.equals import Equals
    from pylogic.structures.class_ import Class
    from pylogic.structures.set_ import Set
    from pylogic.symbol import Symbol
    from pylogic.typing import Term, Unification
    from pylogic.variable import Variable


Props = TypeVarTuple("Props")

TProposition = TypeVar("TProposition", bound="Proposition")
UProposition = TypeVar("UProposition", bound="Proposition")
InferenceRule = TypedDict("InferenceRule", {"name": str, "arguments": list[str]})


####################################################


def get_assumptions(p: Proposition) -> set[Proposition]:
    """
    Given a proposition, return the assumptions that were used to deduce it.
    """
    if p.is_assumption:
        return {p}
    return p.from_assumptions


class Proposition:
    """
    Create a Proposition. A proposition is a declarative logical statement.

    Parameters
    ----------
    name: str
        Name of the proposition.
    is_assumption: bool
        Whether this proposition is an assumption. Assumptions are true only within
        the context they are made.
    is_axiom: bool
        Whether this proposition is an axiom. Axioms are true in all contexts.
    description: str
        A description of what this proposition is.
    args: list[Term] | None
        The arguments of the proposition. If `None`, the proposition has no arguments.

    Attributes
    ----------
    name: str
        Name of the proposition.
    is_assumption: bool
        Whether this proposition is an assumption. Assumptions are true only within
        the context they are made.
    is_axiom: bool
        Whether this proposition is an axiom. Axioms are true in all contexts.
    description: str
        A description of this proposition.
    args: list[Term] | None
        The arguments of the proposition.
    arity: int
        The number of arguments of the proposition.
    is_proven: bool
        Whether the proposition has been proven. If :py:attr:`is_proven` is `False`, the
        proposition is not necessarily false, but it is not proven to be true.
    from_assumptions: set[Proposition]
        The assumptions that were used to deduce this proposition.
    deduced_from: Inference | None
        The inference that was used to deduce this proposition. This will not be
        `None` if the proposition was proven using inference rules. This is
        `None` if :py:attr:`is_proven` is `False`, or if :py:attr:`is_axiom` is `True` while
        :py:attr:`is_asumption` is `False`.

    Example
    -------
    >>> p = Proposition("p", args=[1, 2])
    >>> p.name
    'p'
    >>> p.args
    [Constant(1, deps=()), Constant(2, deps=())]
    >>> p.is_assumption
    False
    """

    # order of operations for propositions (0-indexed)
    # not xor and or => <=> forall forallInSet forallSubsets exists existsInSet existsUnique
    # existsUniqueInSet existsSubset existsUniqueSubset Proposition
    _precedence = 15
    _is_wrapped = False

    # TODO: arguments are not accurate
    _inference_rules: list[InferenceRule] = [
        {"name": "p_substitute", "arguments": ["Side", "Equality"]},
        {"name": "p_and", "arguments": []},
        {"name": "p_and_reverse", "arguments": []},
        {"name": "modus_ponens", "arguments": ["Implies"]},
        {"name": "is_one_of", "arguments": ["And"]},
        {"name": "is_special_case_of", "arguments": ["Forall"]},
        # {"name": "followed_from", "arguments": []},
        {"name": "thus_there_exists", "arguments": ["str", "Term", "list[list[int]]"]},
        # {"name": "thus_forall", "arguments": ["Variable"]},
        {"name": "de_morgan", "arguments": []},
        {"name": "modus_tollens", "arguments": ["Implies"]},
        {"name": "de_morgan", "arguments": []},
        {"name": "contradicts", "arguments": ["Proposition"]},
        {"name": "de_morgan", "arguments": []},
    ]

    def __init__(
        self,
        name: str,
        is_assumption: bool = False,
        is_axiom: bool = False,
        description: str = "",
        args: list[Term] | None = None,
        **kwargs,
    ) -> None:
        from pylogic.helpers import (
            get_class_ns,
            get_consts,
            get_sets,
            get_vars,
            python_to_pylogic,
            type_check_no,
        )
        from pylogic.inference import Inference

        _is_proven: bool = cast(bool, kwargs.get("_is_proven", False))
        _inference: Inference | None = cast(
            Inference | None, kwargs.get("_inference", None)
        )
        _assumptions: set[Proposition] | None = cast(
            set[Proposition] | None, kwargs.get("_assumptions", None)
        )
        name = name.strip()
        assert set(name.split("_")) != {""}, "Proposition name cannot be empty"
        self.name: str = name
        # cannot call _set_is_assumption because _is_proven and is_axiom are not set yet
        self.is_assumption: bool = is_assumption

        self.is_axiom: bool = is_axiom
        for arg in args or []:
            type_check_no(arg, Proposition, str, context="Proposition.__init__")
        self.args: list[Set | Term] = list(map(python_to_pylogic, args or []))
        self.arity: int = len(self.args)
        self._is_proven: bool = _is_proven

        self.is_atomic: bool = True
        self.description: str = description
        if self.is_assumption:
            self.deduced_from: Inference | None = Inference(None, conclusion=self)
            self.from_assumptions = set()
        elif self._is_proven:
            self.deduced_from: Inference | None = _inference
            if self.deduced_from is not None:
                self.deduced_from.conclusion = self
            self.from_assumptions: set[Proposition] = _assumptions or set()
        else:
            self.deduced_from: Inference | None = None
            self.from_assumptions: set[Proposition] = set()

        self.bound_vars: set[Variable] = set()  # Variables that are bound to
        # quantifiers in the proposition.
        self._definition = self

        self.is_todo: bool = False

        self.variables: set[Variable] = set()
        for a in self.args:
            self.variables.update(get_vars(a))
        self.constants: set[Constant] = set()
        for a in self.args:
            self.constants.update(get_consts(a))
        self.sets: set[Set] = set()
        for a in self.args:
            self.sets.update(get_sets(a))
        self.class_ns: set[Class] = set()
        for a in self.args:
            self.class_ns.update(get_class_ns(a))

    @property
    def symbols(self) -> set[Symbol]:
        """
        All the symbols in the proposition. This includes variables and constants.
        """
        return self.variables.union(self.constants)  # type: ignore

    @property
    def atoms(self) -> set[Symbol | Set]:
        """
        All the atomic symbols and sets in the proposition.
        This includes variables, constants, sets and classes.
        """
        # TODO: Maybe include Function
        return self.symbols.union(self.sets).union(self.class_ns)

    def __eq__(self, other: object) -> bool:
        """
        Check if two propositions are equal. For atomic propositions, this will
        check if the names and arguments are equal. For compound propositions,
        this will check if they are of the same type and if all the
        subpropositions are equal.
        """
        if isinstance(other, Proposition):
            return self.name == other.name and self.args == other.args
        return NotImplemented

    @classmethod
    def inference_rules(cls) -> list[str]:
        """
        Return a list of inference rules that are implemented in this class.

        Returns
        -------
        list[str]
            A list of inference rules that are implemented in this class.

        """
        ret_val = []
        for attr, v in cls.__dict__.items():
            if callable(v) and v.__doc__ is not None and "inference rule" in v.__doc__:
                ret_val.append(attr)
        # add from super classes
        for base in cls.__bases__:
            if hasattr(base, "inference_rules"):
                ret_val.extend(base.inference_rules())
        return ret_val
        # return [r["name"] for r in self._inference_rules]

    @property
    def definition(self) -> Proposition:
        """
        A(n expanded) definition of the proposition.
        """
        return self._definition

    def by_definition(self, proven_def: Proposition) -> Self:
        """
        Logical inference rule.
        Given its definition is proven, return a proven version of this
        proposition.

        Parameters
        ----------
        proven_def: Proposition
            The definition of this proposition that is proven.

        Returns
        -------
        Self
            The proven proposition.

        Raises
        ------
        AssertionError
            If the argument does not match the defintion, or is not proven.

        Examples
        --------
        >>> p = constants("p")
        >>> a, b = variables("a", "b")
        >>> divides = Naturals.divides
        >>> prop = ForallInSet(a, Naturals,
        ...     ForallInSet(b, Naturals,
        ...             divides(p, a * b).implies(divides(p, a).or_(divides(p, b)))
        ...     )
        ... ).assume()
        >>> not_0_or_1 = neg(p.equals(0)).and_(neg(p.equals(1))).assume()
        >>> p_prime = Naturals.prime(p).by_definition(not_0_or_1.and_(prop))
        >>> p_prime
        Prime(p)
        >>> p_prime.is_proven
        True
        """
        assert proven_def.is_proven, f"{proven_def} is not proven"
        assert (
            self.definition == proven_def
        ), f"The definition of '{self}' does not match '{proven_def}'\
\n{self.definition}\n != \n{proven_def}"
        from pylogic.inference import Inference

        new_p = self.copy()
        new_p._set_is_proven(True)
        new_p.from_assumptions = get_assumptions(proven_def)
        new_p.deduced_from = Inference(self, conclusion=new_p, rule="by_definition")
        return new_p

    def _set_init_inferred_attrs(self) -> None:
        """
        Set the attributes is_proven, is_assumption, and is_axiom
        after other attributes are set, in case they depend on them.

        Must be called at the end of __init__ for every immediate
        subclass of Proposition that implements _set_is_proven,
        _set_is_assumption, or _set_is_axiom.

        This is called after every __init__, but the methods should not run
        if the attributes are not True. For instance

        ```
        p1 = x.is_in(A, is_assumption=True)
        p2 = x.is_in(A, is_assumption=False)
        ```
        `p2` calling `_set_is_assumption(False)` would affect `x.knowledge_base`
        and future proofs using `x.is_in(A)`.
        """
        try:
            if self.is_assumption:
                self._set_is_assumption(self.is_assumption)
            if self.is_axiom:
                self._set_is_axiom(self.is_axiom)
            if self._is_proven:
                self._set_is_proven(self._is_proven)
        except AttributeError:
            pass

    def _set_is_inferred(self, value: bool) -> None:
        """
        Used in some subclasses like `IsContainedIn` for custom behaviour when a proof is made

        This is a common method called by `_set_is_proven`, `_set_is_assumption`, and `_set_is_axiom`
        """
        pass

    def _set_is_proven(self, value: bool, **kwargs) -> None:
        import pylogic.assumptions_context as ac

        self._is_proven = value
        if value:
            self._set_is_inferred(True)

        # don't add to context for internal use
        if kwargs.get("_internal", False) or (
            kwargs.get("add_to_context", False) is True
        ):  # different for _set_is_assumption
            return

        # context can be None
        context = kwargs.get("context", ac.assumptions_contexts[-1])
        if context is not None and value:
            context._proven.append(self)
        if ac._target_to_prove == self:
            ac._target_to_prove = None

    def _set_is_assumption(self, value: bool, **kwargs) -> None:
        self.is_assumption = value
        if value:
            self._set_is_inferred(True)

        # don't add to context for internal use
        if kwargs.get("_internal", False):
            return

        import pylogic.assumptions_context as ac
        from pylogic.proposition.implies import Implies

        add_to_context = kwargs.get("add_to_context", True)
        if not add_to_context:
            return
        context = kwargs.get("context", ac.assumptions_contexts[-1])
        if context is not None and value:
            context.assumptions.append(self)
        if ac._target_to_prove == self:
            ac._target_to_prove = None
        elif isinstance(ac._target_to_prove, Implies):
            try:
                ac._target_to_prove = (
                    ac._target_to_prove.first_unit_definite_clause_resolve(
                        self, prove=False
                    )
                )
            except (AssertionError, TypeError, ValueError):
                pass

    def _set_is_axiom(self, value: bool) -> None:
        self.is_axiom = value
        if value:
            self._set_is_inferred(True)

    def todo(self, **kwargs) -> Self:
        """
        Mark the proposition as proven, but not yet implemented.

        Returns
        -------
        Self
            The proposition itself.

        Warns
        -----
        UserWarning
            Lets the user know that this proposition is not actually proven yet.
        """
        from pylogic.inference import Inference
        from pylogic.warn import PylogicInternalWarning

        internal = kwargs.get("_internal", False)
        warning_cls = PylogicInternalWarning if internal else UserWarning

        self.is_todo = True
        warnings.warn(
            f"{self} is marked as TODO",
            warning_cls,
        )
        self._set_is_proven(True)
        self.from_assumptions = set()
        self.deduced_from = Inference(self, conclusion=self, rule="todo")
        return self

    def assume(self, **kwargs) -> Self:
        """
        Logical inference rule.

        Mark the proposition as an assumption.

        Returns
        -------
        Self
            The proposition itself.
        """
        self._set_is_assumption(True, **kwargs)
        return self

    def eval_same(self, other: Proposition) -> bool:
        """
        Check if two propositions evaluate to equal propositions.
        We check if the names are equal and if all the corresponding arguments
        evaluate to equal terms.

        Parameters
        ----------
        other: Proposition
            The proposition to compare to.

        Returns
        -------
        bool
            `True` if the propositions are evaluate to the same proposition, `False`
            otherwise.

        Examples
        --------
        >>> p1 = Proposition("p", args=[2])
        >>> p2 = Proposition("p", args=[Add(1, 1)])
        >>> p1.eval_same(p2)
        True
        """
        from pylogic.helpers import eval_same

        return self.name == other.name and all(
            eval_same(self_arg, other_arg)
            for self_arg, other_arg in zip(self.args, other.args)
        )

    def __hash__(self) -> int:
        return hash((self.name, *self.args))

    def __repr__(self) -> str:
        if self.args:
            args_str = tuple(str(a) for a in self.args)
            return f"Proposition({self.name}, {', '.join(args_str)})"
        else:
            return f"Proposition({self.name})"

    def __str__(self) -> str:
        if self.args:
            args_str = tuple(str(a) for a in self.args)
            return f"{self.name}({', '.join(args_str)})"
        else:
            return self.name

    def __copy__(self) -> Self:
        """
        Create a shallow copy of the proposition.
        """
        return self.copy()

    def __bool__(self) -> bool:
        """
        Raises
        ------
        TypeError
            Cannot convert a proposition to a boolean.
        """
        raise TypeError("Cannot convert proposition to bool")

    def __rshift__(
        self, other: Proposition
    ) -> Implies[Self, Proposition] | Implies[And[Self, Proposition], Proposition]:
        """
        Create an implication from this proposition to another. This works when
        :py:attr:`~pylogic.enviroment_settings.settings["PYTHON_OPS_RETURN_PROPS"]` is `True`.

        Parameters
        ----------
        other: Proposition

        Returns
        -------
        Implies[Self, Proposition] | Implies[And[Self, Proposition], Proposition]
            An implication from this proposition to the other proposition.

        Raises
        ------
        TypeError
            If :py:attr:`~pylogic.enviroment_settings.settings["PYTHON_OPS_RETURN_PROPS"]` is `False`, this
            operator returns :py:class:`NotImplemented` and raises a :py:exc:`TypeError`.
        """
        if settings["PYTHON_OPS_RETURN_PROPS"]:
            return self.implies(other)
        return NotImplemented

    def __and__(self, other: Proposition) -> And[Self, Proposition]:
        """
        Create a conjunction from this proposition to another. This works when
        :py:attr:`~pylogic.enviroment_settings.settings["PYTHON_OPS_RETURN_PROPS"]` is `True`.

        Parameters
        ----------
        other: Proposition
            The other proposition to combine with this one.

        Returns
        -------
        And[Proposition, Proposition]
            A conjunction of this proposition and the other proposition.

        Raises
        ------
        TypeError
            If :py:attr:`~pylogic.enviroment_settings.settings["PYTHON_OPS_RETURN_PROPS"]` is `False`, this
            operator returns :py:class:`NotImplemented` and raises a :py:exc:`TypeError`.
        """
        if settings["PYTHON_OPS_RETURN_PROPS"]:
            return self.and_(other)
        return NotImplemented

    def __or__(self, other: Proposition) -> Or[Self, Proposition]:
        """
        Create a disjunction from this proposition to another. This works when
        :py:attr:`~pylogic.enviroment_settings.settings["PYTHON_OPS_RETURN_PROPS"]` is `True`.

        Parameters
        ----------
        other: Proposition
            The other proposition to combine with this one.

        Returns
        -------
        Or[Proposition, Proposition]
            A disjunction of this proposition and the other proposition.

        Raises
        ------
        TypeError
            If :py:attr:`~pylogic.enviroment_settings.settings["PYTHON_OPS_RETURN_PROPS"]` is `False`, this
            operator returns :py:class:`NotImplemented` and raises a :py:exc:`TypeError`.
        """
        if settings["PYTHON_OPS_RETURN_PROPS"]:
            return self.or_(other)
        return NotImplemented

    def __xor__(self, other: Proposition) -> ExOr[Self, Proposition]:
        """
        Create an exclusive disjunction from this proposition to another. This works when
        :py:attr:`~pylogic.enviroment_settings.settings["PYTHON_OPS_RETURN_PROPS"]` is `True`.

        Parameters
        ----------
        other: Proposition
            The other proposition to combine with this one.

        Returns
        -------
        ExOr[Proposition, Proposition]
            An exclusive disjunction of this proposition and the other proposition.

        Raises
        ------
        TypeError
            If :py:attr:`~pylogic.enviroment_settings.settings["PYTHON_OPS_RETURN_PROPS"]` is `False`, this
            operator returns :py:class:`NotImplemented` and raises a :py:exc:`TypeError`.
        """
        if settings["PYTHON_OPS_RETURN_PROPS"]:
            return self.xor(other)
        return NotImplemented

    def __invert__(self) -> Not[Self]:
        """
        Create a negation of this proposition. This works when
        :py:attr:`~pylogic.enviroment_settings.settings["PYTHON_OPS_RETURN_PROPS"]` is `True`.

        Returns
        -------
        Not[Self]
            A negation of this proposition.

        Raises
        ------
        TypeError
            If :py:attr:`~pylogic.enviroment_settings.settings["PYTHON_OPS_RETURN_PROPS"]` is `False`, this
            operator returns :py:class:`NotImplemented` and raises a :py:exc:`TypeError`.
        """
        if settings["PYTHON_OPS_RETURN_PROPS"]:
            from pylogic.proposition.not_ import neg

            return neg(self)
        return NotImplemented

    def _latex(self, printer=None) -> str:
        """
        Return a LaTeX representation of the proposition.

        Returns
        -------
        str
            A LaTeX representation of the proposition.
        """
        from pylogic.helpers import latex

        args_latex = [latex(a) for a in self.args]
        if not args_latex:
            return rf"\text{{{self.name}}}"
        return rf"\text{{{self.name}}}\left({', '.join(args_latex)}\right)"

    def _repr_latex_(self) -> str:
        """
        Return a LaTeX representation of the proposition for Jupyter notebooks.
        This is used to render the proposition in LaTeX format.
        """
        return f"$${self._latex()}$$"

    @property
    def is_proven(self) -> bool:
        """
        Whether the proposition has been proven. If :py:attr:`is_proven` is `False`, the
        proposition is not necessarily false, but it is not proven to be true.
        """
        return self._is_proven or self.is_assumption or self.is_axiom

    def as_text(self, *, _indent=0) -> str:
        """
        Return a text representation of the proposition. Subpropositions
        are indented further right. One indentation is 2 spaces.

        Returns
        -------
        str
            A text representation of the proposition.
        """
        return "  " * _indent + repr(self) + "\n"

    def describe(self, *, _indent=0) -> str:
        """
        Return a description of the proposition. If no description is set,
        it calls :py:meth:`as_text` to get a text representation of the proposition.

        Returns
        -------
        str
            A description of the proposition.
        """
        if self.description:
            return "  " * _indent + self.description + "\n"
        return self.as_text(_indent=_indent)

    def set_description(self, description: str) -> Self:
        """
        Set the description of the proposition.

        Parameters
        ----------
        description: str
            The description of the proposition.

        Returns
        -------
        Self
            The proposition itself.
        """
        self.description = description
        return self

    set_desc = set_description

    def copy(self) -> Self:
        """
        Create a shallow copy of the proposition.
        The copy keeps the same references to the arguments, assumptions, and
        inference as the original proposition.

        Returns
        -------
        Self
            A shallow copy of the proposition.
        """
        return self.__class__(
            self.name,
            is_assumption=self.is_assumption,
            is_axiom=self.is_axiom,
            description=self.description,
            args=self.args,
            _is_proven=self._is_proven,
            _inference=self.deduced_from,
            _assumptions=self.from_assumptions,
        )

    def deepcopy(self) -> Self:
        """
        Create a deep copy of the proposition.
        The copy creates new copies of the arguments of the proposition.
        The copy keeps the same references to the assumptions and inference
        as the original proposition.

        Returns
        -------
        Self
            A deep copy of the proposition.
        """
        from pylogic.helpers import is_python_numeric

        return self.__class__(
            self.name,
            is_assumption=self.is_assumption,
            is_axiom=self.is_axiom,
            description=self.description,
            args=[a.deepcopy() if not is_python_numeric(a) else a for a in self.args],  # type: ignore
            _is_proven=self._is_proven,
            _inference=self.deduced_from,
            _assumptions=self.from_assumptions,
        )

    def replace(
        self,
        replace_dict: dict[Term, Term],
        positions: list[list[int]] | None = None,
        equal_check: Callable[[Term, Term], bool] | None = None,
    ) -> Proposition:
        r"""
        This function currently replaces Terms in the proposition with other Terms.
        It does not replace Propositions.

        For each key in `replace_dict`, we replace it in the proposition with the
        corresponding new value.

        `positions` is a list of lists of integers representing the occurences
        of the old values in the proposition. Each list of integers represents
        a path to the value in the proposition tree.
        Each integer in the list represents the index of the subproposition (or
        subexpression) in the list of subpropositions/arguments of the parent
        proposition.

        Parameters
        ----------
        replace_dict: dict[Term, Term]
            A dictionary where the keys are the :py:class:`Term`\ s to be replaced
            and the values are the new :py:class:`Term`\ s.
        positions: list[list[int]] | None
            This is a list containing the positions of the old values in this
            instance.
            If `None`, we will replace for all occurences of the old values with
            the new values.
            The nested list represents the path we need to go down in the
            proposition tree.

            TODO: finish replace, document replacing the quantified variables
            as well

            For example, if self is
            `(forall x: (p1 x -> p2 x) /\ (p3 x) /\ (p4 x)) -> (p5 x)`
            current_val = x
            new_val = p
            and positions = [[0, 0, 0], [0, 2], [1]]
            we end up with
            exists q: (forall x: (p1 q -> p2 x) /\ (p3 x) /\ (p4 q)) -> (p5 q)
            The quantified variable in a forall is never replaced itself. Due to this,
            the positions array for forall goes directly into the inner proposition.
            Same for exists.
            In the example above, the first list [0,0,0] refers to the x in p1 x, not (p1 x -> p2 x).
        equal_check: Callable[[Term, Term], bool] | None
            A function that takes two arguments and returns True if they compare
            equal. By default, it uses the `==` operator.

        Returns
        -------
        Proposition
            A new proposition with the replaced values.

        Examples
        --------
        >>> x, y, a = variables("x", "y", "a")
        >>> p1, p2, p3,  p4, p5 = predicates("p1", "p2", "p3", "p4", "p5")
        >>> prop1 = Forall(x, p1(x, y).implies(p2(y)).and_(p3(y), p4(y))).implies(p5(y))
        >>> prop1.replace({y: a}, positions=[[0, 0, 0], [0, 2], [1]])
        (forall x: ((p1(x, a) -> p2(y)) /\ p3(y) /\ p4(a))) -> p5(a)
        >>> prop1.replace({x: a}, positions=[[0, 0, 0]])
        (forall a: ((p1(a, y) -> p2(y)) /\ p3(y) /\ p4(y))) -> p5(y)

        Note
        -----
        In the example above, the first list [0,0,0] refers to the proposition
        `p1(x, y)`, so in the first call to :py:meth:`replace`, all occurences
        of `y` in `p1(x, y)` are replaced with `a`.
        """
        from pylogic.expressions.expr import Expr

        equal_check = equal_check or (lambda x, y: x == y)
        new_p_args = self.args.copy()
        index = -1
        for arg in new_p_args:
            index += 1
            if (positions is not None) and not [index] in positions:
                continue
            if isinstance(arg, Expr):
                new_p_args[index] = arg.replace(replace_dict, equal_check=equal_check)
            else:
                for current_val in replace_dict:
                    new_val = replace_dict[current_val]
                    if equal_check(current_val, arg):
                        new_p_args[index] = new_val
                        break

        new_p = self.__class__(
            self.name,
            is_assumption=False,
            args=new_p_args,
        )
        return new_p

    def substitute(self, side: Side | str, equality: "Equals", **kwargs) -> Proposition:
        """
        Logical inference rule.

        We substitute the required side of the equality into this proposition.

        Parameters
        ----------
        side: Side
            :py:attr:`~pylogic.helpers.Side.LEFT` or :py:attr:`~pylogic.helpers.Side.RIGHT`

            The side of the equality to appear in the result.
        equality: Equals
            An equality proposition. We look for the other side of the equality
            in self and replace it with the required `side`. So if `side` is
            :py:attr:`~pylogic.helpers.Side.LEFT`, the left side of the equality
            will appear in the result.

        Returns
        -------
        Proposition
            A new proposition with the side of the equality substituted into
            this proposition.

        TODO: If `substitute_into` raises an exception, should we document it here?

        Examples
        --------
        >>> x, y = variables("x", "y")
        >>> A = Set("A")
        >>> p1 = x.is_in(A)
        >>> p2 = p1.substitute("right", x.equals(y))
        >>> p2
        y in A
        """
        if self.is_proven and equality.is_proven and not kwargs:
            from pylogic.inference import Inference

            kwargs = dict(
                _is_proven=True,
                _inference=Inference(self, equality, rule="p_substitute"),
                _assumptions=get_assumptions(self).union(get_assumptions(equality)),
            )

        return equality.substitute_into(side, self, **kwargs)

    def p_substitute(self, side: Side | str, equality: Equals) -> Self:
        """
        Parameters
        ----------
        side: Side
            :py:attr:`~pylogic.helpers.Side.LEFT` or :py:attr:`~pylogic.helpers.Side.RIGHT`
        equality: Equals
            An equality proposition. We look for the other side of the equality
            in self and replace it with the 'side'.
        .. deprecated::0.0.1
            Use :py:meth:`substitute` instead.

        Returns
        -------
        Proposition
            a proven proposition.
        """
        from pylogic.inference import Inference

        assert self.is_proven, f"{self} is not proven"
        assert equality.is_proven, f"{equality} is not proven"
        new_p = self.substitute(
            side,
            equality,
            _is_proven=True,
            _inference=Inference(self, equality, rule="p_substitute"),
            _assumptions=get_assumptions(self).union(get_assumptions(equality)),
        )
        return new_p

    def by_inspection_check(self) -> bool | None:
        """
        Check if this proposition is provable by inspection.
        This is meant to represent proving a statement by applying some obvious
        algorithm. For instance, we can prove that 5 is prime by inspection.

        Returns
        -------
        bool | None
            `True` if self is provable by inspection, `False` if
            its negation is provable by inspection, and `None` if neither is provable.
        """
        return None

    def by_inspection(self) -> Self:
        """
        Logical inference rule. Try to prove the proposition by inspection.

        This is meant to represent proving a statement by applying some obvious
        algorithm or check. For instance, we can prove that 5 is prime by
        inspection.

        Returns
        -------
        Self
            A new proposition that is proven by inspection.

        Raises
        ------
        ValueError
            If the proposition cannot be proven by inspection.
        """
        from pylogic.inference import Inference

        if self.by_inspection_check():
            new_p = self.copy()
            new_p._set_is_proven(True)
            new_p.from_assumptions = set()
            new_p.deduced_from = Inference(self, conclusion=new_p, rule="by_inspection")
            return new_p
        else:
            raise ValueError(f"{self} cannot be proven by inspection")

    # @overload
    # def implies(
    #     self,
    #     other: Implies[TProposition, UProposition],
    #     is_assumption: bool = False,
    #     **kwargs,
    # ) -> Implies[And[Self, TProposition], UProposition]: ...

    # @overload
    # def implies(
    #     self, other: TProposition, is_assumption: bool = False, **kwargs
    # ) -> Implies[Self, TProposition]: ...

    def implies(
        self,
        other: TProposition | Implies[TProposition, UProposition],
        is_assumption: bool = False,
        de_nest: bool = True,
        **kwargs,
    ) -> Implies[Self, TProposition] | Implies[And[Self, TProposition], UProposition]:
        r"""
        Logical inference rule.
        Create an implication from this proposition to another.

        If this proposition is the same as `other`, or this proposition is
        `contradiction`, or `other` is proven, the resulting implication is
        proven.

        Parameters
        ----------
        other: TProposition | Implies[TProposition, UProposition]
            The other proposition to combine with this one.
        is_assumption: bool
            If `True`, the resulting proposition is an assumption.
        de_nest: bool
            If `True`, we de-nest the implication. This means that if `other` is
            an implication, we combine this proposition with the antecedent of
            the implication (to make a conjunction) and return a new implication.

            If `False`, we return the nested implication.

        Returns
        -------
        Implies[Self, TProposition] | Implies[And[Self, TProposition], UProposition]
            An implication from this proposition to the other proposition.

        Examples
        --------
        >>> p, q, r = propositions("p", "q", "r")
        >>> qr = q.implies(r)
        >>> qr
        q -> r
        >>> p.implies(qr)
        p /\ q -> r
        >>> p.implies(qr, de_nest=False)
        p -> (q -> r)
        """
        from pylogic.inference import Inference
        from pylogic.proposition.implies import Implies
        from pylogic.proposition.not_ import Not

        if de_nest and isinstance(other, Implies) and not isinstance(other, Not):
            ret_val = self.and_(other.antecedent).implies(
                other.consequent, is_assumption=is_assumption, **kwargs
            )
        else:
            ret_val = Implies(self, other, is_assumption, **kwargs)

        prove = False
        rule = None
        # assumption is already proven
        if kwargs.get("dont_prove") or is_assumption:
            prove = False
        elif other.is_proven:
            prove = True
            rule = "left_weakening"
        elif self == other:
            prove = True
            rule = "tautology"
        if prove:
            assert rule is not None
            ret_val._set_is_proven(True)
            ret_val.from_assumptions = get_assumptions(other)
            ret_val.deduced_from = Inference(self, other, conclusion=ret_val, rule=rule)
        return ret_val

    def iff(
        self, other: TProposition, is_assumption: bool = False, **kwargs
    ) -> Iff[Self, TProposition]:
        r"""
        Create a biconditional between this proposition and another.

        Parameters
        ----------
        other: TProposition
            The other proposition to combine with this one.
        is_assumption: bool
            If `True`, the resulting proposition is an assumption.

        Returns
        -------
        Iff[Self, TProposition]
            A biconditional between this proposition and the other proposition.

        Examples
        --------
        >>> p, q = propositions("p", "q")
        >>> p.iff(q)
        p <-> q
        """
        from pylogic.proposition.iff import Iff

        return Iff(self, other, is_assumption=is_assumption, **kwargs)

    @overload
    def and_(
        self,
        *others: *Props,
        is_assumption: bool = False,
        allow_duplicates: Literal[True] = True,
        **kwargs,
    ) -> And: ...

    @overload
    def and_(
        self,
        *others: *Props,
        is_assumption: bool = False,
        allow_duplicates: bool = False,
        **kwargs,
    ) -> And[Self, *Props]: ...

    def and_(
        self,
        *others: *Props,
        is_assumption: bool = False,
        allow_duplicates: bool = False,
        **kwargs,
    ) -> And[Self, *Props] | And:
        r"""
        Logical inference rule.

        Combine this proposition with others using a conjunction.
        Contiguous :py:class:`~pylogic.proposition.and_.And` objects are
        combined into one :py:class:`~pylogic.proposition.and_.And` proposition
        to reduce nesting.

        If all propositions are proven, the resulting proposition is proven.

        Parameters
        ----------
        others: *Props
            The other proposition(s) to combine with this one.
        is_assumption: bool
            If `True`, the resulting proposition is an assumption.
        allow_duplicates: bool
            If True, we do not remove duplicate propositions.

        Returns
        -------
        And[Self, *Props] | And
            A conjunction of this proposition and the other proposition(s).
            If all propositions are proven, the resulting proposition is proven.

        Examples
        --------
        >>> p1 = x.is_in(A)
        >>> p2 = y.is_in(B)
        >>> p3 = p1.and_(p2)
        >>> p3
        x in A /\ y in B
        """
        from pylogic.inference import Inference
        from pylogic.proposition.and_ import And

        props = []
        first_not_proven = None
        for p in (self, *others):
            if not p.is_proven and first_not_proven is None:
                first_not_proven = p
            if isinstance(p, And):
                props.extend(p.de_nest().propositions)
            else:
                props.append(p)
        if first_not_proven is None:
            kwargs["_is_proven"] = True
            kwargs["_assumptions"] = get_assumptions(self).union(
                *[get_assumptions(o) for o in others]  # type: ignore
            )
            kwargs["_inference"] = Inference(self, *others, rule="all_proven")

        new_p = And(*props, is_assumption=is_assumption, **kwargs)  # type: ignore
        if not allow_duplicates:
            return new_p.remove_duplicates()
        return new_p

    @overload
    def and_reverse(
        self,
        *others: *Props,
        is_assumption: bool = False,
        allow_duplicates: Literal[True] = True,
        **kwargs,
    ) -> And: ...

    @overload
    def and_reverse(
        self,
        *others: *Props,
        is_assumption: bool = False,
        allow_duplicates: bool = False,
        **kwargs,
    ) -> And[*Props, Self]: ...

    def and_reverse(
        self,
        *others: *Props,
        is_assumption: bool = False,
        allow_duplicates: bool = False,
        **kwargs,
    ) -> And[*Props, Self] | And:
        r"""
        Logical inference rule.
        Combine this proposition with others using a conjunction, with self at
        the end.
        Contiguous :py:class:`~pylogic.proposition.and_.And` objects are combined
        into one :py:class:`~pylogic.proposition.and_.And` proposition to reduce
        nesting.

        Parameters
        ----------
        others: *Props
            The other proposition(s) to combine with this
            one.
        is_assumption: bool
            If `True`, the resulting proposition is an assumption.
        allow_duplicates: bool
            If True, we do not remove duplicate propositions.

        Returns
        -------
        And[*Props, Self] | And
            A conjunction of this proposition and the other proposition(s).
            If all propositions are proven, the resulting proposition is proven.

        Examples
        --------
        >>> p1 = x.is_in(A)
        >>> p2 = y.is_in(B)
        >>> p3 = p1.and_reverse(p2)
        >>> p3
        y in B /\ x in A
        """
        first = others[0]
        rest = others[1:]
        return first.and_(  # type:ignore
            *rest,
            self,
            is_assumption=is_assumption,
            allow_duplicates=allow_duplicates,
            **kwargs,
        )

    def or_(
        self,
        *others: *Props,
        is_assumption: bool = False,
        allow_duplicates: bool = False,
        **kwargs,
    ) -> Or[Self, *Props] | Or:
        r"""
        Logical inference rule.

        Combine this proposition with others using a disjunction.
        Contiguous :py:class:`~pylogic.proposition.or_.Or` objects are combined
        into one :py:class:`~pylogic.proposition.or_.Or` proposition to reduce
        nesting.

        If any of the propositions is proven, the resulting proposition is
        proven.

        Parameters
        ----------
        others: *Props
            The other proposition(s) to combine with this
            one.
        is_assumption: bool
            If `True`, the resulting proposition is an assumption.
        allow_duplicates: bool
            If `True`, we do not remove duplicate propositions.

        Returns
        -------
        Or[Self, *Props] | Or
            A disjunction of this proposition and the other proposition(s).
            If any of the propositions is proven, the resulting proposition is
            proven.

        Examples
        --------
        >>> p1 = x.is_in(A)
        >>> p2 = y.is_in(B)
        >>> p3 = p1.or_(p2)
        >>> p3
        x in A \/ y in B
        """
        from pylogic.inference import Inference
        from pylogic.proposition.or_ import Or

        props = []
        first_proven = None
        for p in (self, *others):
            if p.is_proven and first_proven is None:
                first_proven = p
            if isinstance(p, Or):
                props.extend(p.de_nest().propositions)
            else:
                props.append(p)
        if first_proven is not None:
            kwargs["_is_proven"] = True
            kwargs["_assumptions"] = get_assumptions(self).union(
                *[get_assumptions(o) for o in others]  # type: ignore
            )
            kwargs["_inference"] = Inference(self, *others, rule="one_proven")
        new_p = Or(*props, is_assumption=is_assumption, **kwargs)  # type:ignore
        if not allow_duplicates:
            return new_p.remove_duplicates()
        return new_p

    def or_reverse(
        self,
        *others: *Props,
        is_assumption: bool = False,
        allow_duplicates: bool = False,
        **kwargs,
    ) -> Or[*Props, Self] | Or:
        r"""
        Logical inference rule.
        Combine this proposition with others using a disjunction, with self at
        the end.
        Contiguous :py:class:`~pylogic.proposition.or_.Or` objects are combined
        into one :py:class:`~pylogic.proposition.or_.Or` proposition to reduce
        nesting.

        Parameters
        ----------
        others: *Props
            The other proposition(s) to combine with this
            one.
        is_assumption: bool
            If `True`, the resulting proposition is an assumption.
        allow_duplicates: bool
            If `True`, we do not remove duplicate propositions.

        Returns
        -------
        Or[*Props, Self] | Or
            A disjunction of this proposition and the other proposition(s).
            If any of the propositions is proven, the resulting proposition is
            proven.

        Examples
        --------
        >>> p1 = x.is_in(A)
        >>> p2 = y.is_in(B)
        >>> p3 = p1.or_reverse(p2)
        >>> p3
        y in B \/ x in A
        """
        first = others[0]
        rest = others[1:]
        return first.or_(  # type: ignore
            *rest,
            self,
            is_assumption=is_assumption,
            allow_duplicates=allow_duplicates,
            **kwargs,
        )

    def xor(
        self,
        *others: *Props,
        is_assumption: bool = False,
        allow_duplicates: bool = False,
        **kwargs,
    ) -> ExOr[Self, *Props] | ExOr:
        """
        Combine this proposition with others using an exclusive or.
        Contiguous :py:class:`~pylogic.proposition.exor.ExOr` objects are
        combined into one :py:class:`~pylogic.proposition.exor.ExOr` sequence to
        reduce nesting.

        Parameters
        ----------
        others: *Props
            The other proposition(s) to combine with this one.
        is_assumption: bool
            If `True`, the resulting proposition is an assumption.
        allow_duplicates: bool
            If `True`, we do not remove duplicate propositions.

        Returns
        -------
        ExOr[Self, *Props] | ExOr
            An exclusive disjunction of this proposition and the other
            proposition(s).

        Examples
        --------
        >>> p1 = x.is_in(A)
        >>> p2 = y.is_in(B)
        >>> p3 = p1.xor(p2)
        >>> p3
        x in A xor y in B
        """
        from pylogic.proposition.exor import ExOr

        props = []
        for p in (self, *others):
            if isinstance(p, ExOr):
                props.extend(p.de_nest().propositions)
            else:
                props.append(p)
        new_p = ExOr(*props, is_assumption=is_assumption, **kwargs)  # type:ignore
        if not allow_duplicates:
            return new_p.remove_duplicates()
        return new_p

    def xor_reverse(
        self,
        *others: *Props,
        is_assumption: bool = False,
        allow_duplicates: bool = False,
        **kwargs,
    ) -> ExOr[*Props, Self] | ExOr:
        """
            Combine this proposition with others using an exclusive or, with self at
            the end.
        Contiguous :py:class:`~pylogic.proposition.exor.ExOr` objects are
            combined into one :py:class:`~pylogic.proposition.exor.ExOr` sequence to
            reduce nesting.

            Parameters
            ----------
            others: *Props
                The other proposition(s) to combine with this one.
            is_assumption: bool
                If `True`, the resulting proposition is an assumption.
            allow_duplicates: bool
                If `True`, we do not remove duplicate propositions.

            Returns
            -------
            ExOr[*Props, Self] | ExOr
                An exclusive disjunction of this proposition and the other
                proposition(s).

            Examples
            --------
            >>> p1 = x.is_in(A)
            >>> p2 = y.is_in(B)
            >>> p3 = p1.xor_reverse(p2)
            >>> p3
            y in B xor x in A
        """
        first = others[0]
        rest = others[1:]
        return first.xor(  # type:ignore
            *rest,
            self,
            is_assumption=is_assumption,
            allow_duplicates=allow_duplicates,
            **kwargs,
        )

    def p_and(
        self, *others: *Props, allow_duplicates: bool = False
    ) -> And[Self, *Props]:
        """
        Same as and_, but returns a proven proposition when self and all others are proven.

        Deprecated since 0.0.1.
        Use :py:meth:`and_` instead.
        """
        from pylogic.inference import Inference

        assert len(others) > 0, "Must provide at least one proposition"
        assert self.is_proven, f"{self} is not proven"
        for o in others:
            assert o.is_proven, f"{o} is not proven"  # type:ignore
        all_assumptions = get_assumptions(self).union(
            *[get_assumptions(o) for o in others]  # type: ignore
        )
        new_p = self.and_(
            *others,
            allow_duplicates=allow_duplicates,
            _is_proven=True,
            _assumptions=all_assumptions,
            _inference=Inference(self, *others, rule="p_and"),
        )
        return new_p

    def p_and_reverse(
        self, *others: *Props, allow_duplicates: bool = False
    ) -> And[*Props, Self]:
        """Logical inference rule.
        Same as and_reverse, but returns a proven proposition when self and all others are proven.

        Deprecated since 0.0.1.
        Use :py:meth:`and_reverse` instead.
        """
        from pylogic.inference import Inference

        assert len(others) > 0, "Must provide at least one proposition"
        assert self.is_proven, f"{self} is not proven"
        for o in others:
            assert o.is_proven, f"{o} is not proven"  # type:ignore
        all_assumptions = get_assumptions(self).union(
            *[get_assumptions(o) for o in others]  # type:ignore
        )
        new_p = self.and_reverse(
            *others,
            allow_duplicates=allow_duplicates,
            _is_proven=True,
            _assumptions=all_assumptions,
            _inference=Inference(self, *others, rule="p_and_reverse"),
        )
        return new_p

    def modus_ponens(
        self, other: Implies[Self, TProposition] | Iff[Self, TProposition], **kwargs
    ) -> TProposition:
        """
        Logical inference rule.

        Parameters
        ----------
        other: Implies[Self, TProposition] | Iff[Self, TProposition]
            Must be an implication that has been proven whose antecedent is
            equal to this proposition.

        Returns
        -------
        Proposition
            The conclusion of the implication. This is a new proposition that
            is proven.

        Raises
        ------
        AssertionError
            If the propositions are not proven or the other proposition is not
            an implication or does not have this proposition as its antecedent.

        Examples
        --------
        >>> p1 = prop("P").assume() # P
        >>> p2 = prop("P").implies(prop("Q")).assume() # P -> Q
        >>> p3 = p1.modus_ponens(p2) # infer Q
        >>> p3, p3.is_proven
        (Q, True)
        """
        # TODO: add **kwargs to allow easy addition of kwargs
        # like prove to all inference rules
        # currently in modus_ponens, in_particular, by_predicate
        from pylogic.inference import Inference
        from pylogic.proposition.iff import Iff
        from pylogic.proposition.implies import Implies

        assert isinstance(other, (Implies, Iff)), f"{other} is not an implication"
        assert other.left == self, f"{other.left} is not the same as {self}"
        new_p = other.right.copy()
        if kwargs.get("prove", True) is False:
            return new_p
        assert self.is_proven, f"{self} is not proven"
        assert other.is_proven, f"{other} is not proven"
        new_p._set_is_proven(True)
        new_p.deduced_from = Inference(
            self, other, conclusion=new_p, rule="modus_ponens"
        )
        new_p.from_assumptions = get_assumptions(self).union(get_assumptions(other))
        return new_p

    mp = fn_alias(modus_ponens, "mp")

    # @overload
    # def modus_tollens(
    #     self, other: Implies[Not[TProposition], Not[Self]]
    # ) -> TProposition: ...

    # @overload
    # def modus_tollens(
    #     self, other: Implies[TProposition, Not[Self]]
    # ) -> Not[TProposition]: ...

    def modus_tollens(
        self,
        other: (
            Implies[Not[TProposition], Not[Self]]
            | Implies[TProposition, Not[Self]]
            | Iff
        ),
    ) -> TProposition | Not[TProposition]:
        """
        Logical inference rule.

        Parameters
        ----------
        other: Implies[Not[TProposition], Not[Self]] | Implies[TProposition, Not[Self]]
            Must be an implication that has been proven whose consequent is
            equal to the negation of this proposition.

        Returns
        -------
        Proposition
            The negation of the antecedent of the implication. This is a new
            proposition that is proven.

        Raises
        ------
        AssertionError
            If the propositions are not proven or the other proposition is not
            an implication or does not have this proposition as its consequent's
            negation.

        Examples
        --------
        >>> p1 = neg(prop("P")).assume() # ~P
        >>> p2 = prop("Q").implies(prop("P")).assume() # Q -> P
        >>> p3 = p1.modus_tollens(p2) # infer ~Q
        >>> p3, p3.is_proven
        (~Q, True)
        """
        from pylogic.inference import Inference
        from pylogic.proposition.iff import Iff
        from pylogic.proposition.implies import Implies
        from pylogic.proposition.not_ import are_negs, neg

        assert self.is_proven, f"{self} is not proven"
        assert other.is_proven, f"{other} is not proven"
        assert isinstance(other, (Implies, Iff)), f"{other} is not an implication"
        assert are_negs(
            other.right, self
        ), f"{other.right} is not the negation of {self}"
        # I'm using copy here because neg(Not(p)) returns p,
        # and we should avoid proving p in a different place.
        n_other_ante = neg(other.left).copy()
        new_p = n_other_ante
        new_p._set_is_proven(True)
        new_p.deduced_from = Inference(
            self, other, conclusion=new_p, rule="modus_tollens"
        )
        new_p.from_assumptions = get_assumptions(self).union(get_assumptions(other))
        return new_p  # type:ignore

    mt = fn_alias(modus_tollens, "mt")

    def is_one_of(self, other: And, *, __recursing: bool = False) -> Self:
        r"""
        Logical inference rule.
        If we have proven other, we can prove any of the propositions in it.
        other: And
            Must be a conjunction that has been proven where one of the propositions is self.

        Examples
        --------
        >>> p1 = prop("P")
        >>> p2 = prop("Q")
        >>> p3 = prop("R")
        >>> p4 = And(p1, p2, p3).assume()
        >>> p5 = p1.is_one_of(p4)
        >>> p5, p5.is_proven
        (P, True)
        """
        if not __recursing:
            assert other.is_proven, f"{other} is not proven"
        from pylogic.inference import Inference
        from pylogic.proposition.and_ import And

        for p in other.propositions:
            if p == self:
                new_p = self.copy()
                new_p._set_is_proven(True)
                new_p.deduced_from = Inference(
                    self, other, conclusion=new_p, rule="is_one_of"
                )
                new_p.from_assumptions = get_assumptions(other).copy()
                return new_p
            elif isinstance(p, And):
                try:
                    return self.is_one_of(p, __recursing=True)
                except ValueError:
                    continue
        raise ValueError(f"{self} is not in {other}")

    def is_special_case_of(self, other: Forall[Self]) -> Self:
        """
        Logical inference rule.
        other: Proposition
            A proven forall proposition that implies this proposition.

        Examples
        --------
        >>> p1 = prop("P", 1)
        >>> p2_proven = Forall(x, prop("P", x)).assume()
        >>> p1_proven = p1.is_special_case_of(p2_proven)
        >>> p1_proven.is_proven
        True
        """
        from pylogic.inference import Inference
        from pylogic.proposition.quantified.forall import Forall

        assert isinstance(other, Forall), f"{other} is not a forall statement"
        assert other.is_proven, f"{other} is not proven"
        unif = other.inner_proposition.unify(self)
        condition1 = isinstance(unif, dict) and len(unif) == 1
        condition2 = False
        if condition1:
            try:
                condition2 = other.in_particular(unif[other.variable]) == self  # type: ignore
            except KeyError:
                condition2 = False
        if condition2 or (unif is True):
            new_p = self.copy()
            new_p._set_is_proven(True)
            new_p.deduced_from = Inference(
                self, other, conclusion=new_p, rule="is_special_case_of"
            )
            new_p.from_assumptions = get_assumptions(other).copy()
            return new_p
        raise ValueError(f"{self} is not a special case of {other}")

    @overload
    def followed_from(
        self, assumption: TProposition, **kwargs
    ) -> Implies[TProposition, Self]: ...

    @overload
    def followed_from(
        self, *assumptions: *Props, **kwargs
    ) -> Implies[And[*Props], Self]: ...

    def followed_from(self, *assumptions, **kwargs):  # type: ignore
        """
        Given self is proven, return a new proposition that is an implication of
        the form And(*assumptions) -> self.
        *assumptions: Proposition
            Propositions that implied this proposition.
        This function only accepts propositions that were explicitly declared as
        assumptions and used to deduce self.

        **Note** that after this function is called, the assumptions are no longer
        considered assumptions. You would need to assume them again if you want to
        use them in another deduction.
        """
        from pylogic.inference import Inference
        from pylogic.warn import PylogicInternalWarning

        assert self.is_proven, f"{self} is not proven"
        _internal_tactic = kwargs.get("_internal_tactic", False)
        assert len(assumptions) > 0, "Must provide at least one other assumption"
        for a in assumptions:
            assert a.is_assumption, f"{a} is not an assumption"
            if a not in self.from_assumptions:
                if _internal_tactic:
                    warning_cls = PylogicInternalWarning
                else:
                    warning_cls = UserWarning
                warnings.warn(
                    f"{a} was not used to deduce {self}",
                    warning_cls,
                )
        from pylogic.proposition.and_ import And
        from pylogic.proposition.implies import Implies

        if len(assumptions) == 1:
            assumptions[0]._set_is_assumption(False)
            assumptions[0]._set_is_proven(False)
            new_p = cast(
                Implies[Proposition, Self], assumptions[0].implies(self)  # type: ignore
            )
        else:
            for a in assumptions:
                # this has been used to prove an implication so
                # we don't want it to be an assumption anymore
                a._set_is_assumption(False)
                a._set_is_proven(False)
            new_p = cast(Implies[And[*Props], Self], And(*assumptions).implies(self))  # type: ignore
        new_p._set_is_proven(True)
        new_p.deduced_from = Inference(
            self, *assumptions, conclusion=new_p, rule="followed_from"  # type:ignore
        )
        new_p.from_assumptions = self.from_assumptions - set(assumptions)
        return new_p

    def thus_there_exists(
        self,
        existential_var: str,
        expression_to_replace: Term,
        set_: Set | Variable | Class | None = None,
        expression_to_replace_is_in_set: (
            IsContainedIn[Term, Set | Variable | Class] | None
        ) = None,
        latex_name: str | None = None,
        positions: list[list[int]] | None = None,
    ) -> Exists[Self]:
        r"""
        Logical inference rule.
        Given self is proven, return a new proposition that there exists an existential_var such that
        self is true, when self is expressed in terms of that existential_var.
        For example, if self is x^2 + x > 0, existential_var is y and expression_to_replace is x^2, then
        we return the proven proposition Exists y: y + x > 0.

        existential_var: str
            A new variable that is introduced into our new existential proposition.
        expression_to_replace: Set | SympyExpression
            An expression that is replaced by the new variable.
        set_: Set
            The set in which the existential variable is contained.
        expression_to_replace_is_in_set: IsContainedIn
            A proposition that states that the expression_to_replace is in the set_.
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

        Examples
        --------
        >>> p1 = prop("P", 1).assume() # P(1)
        >>> p2 = p1.thus_there_exists("x", 1)
        >>> p2, p2.is_proven
        (exists x: P(x), True)
        """
        assert self.is_proven, f"{self} is not proven"
        from pylogic.helpers import find_first, python_to_pylogic
        from pylogic.inference import Inference
        from pylogic.proposition.quantified.exists import Exists, ExistsInSet
        from pylogic.variable import Variable

        expression_to_replace = python_to_pylogic(expression_to_replace)

        # Check that the expression to replace does not depend on any bound variables
        # prevent the sequence
        # forall a: P(x0(a), a) -> exists x: forall a: P(x, a)
        if isinstance(expression_to_replace, Variable):
            first_not_in_atoms_or_bound = find_first(
                lambda x: (x.is_bound),
                expression_to_replace.independent_dependencies,
            )
            if first_not_in_atoms_or_bound[1] is not None:
                raise ValueError(
                    f"{first_not_in_atoms_or_bound[1]} is not in the atoms of {self}, or is bound already, \
and is a dependency of {expression_to_replace}"
                )
        if set_ is None:
            exists_cls = Exists
        else:
            exists_cls = ExistsInSet
            if expression_to_replace_is_in_set is None:
                # try to prove by inspection
                expression_to_replace.is_in(set_).by_inspection()
            else:
                assert (
                    isinstance(expression_to_replace_is_in_set, IsContainedIn)
                    and expression_to_replace_is_in_set.left == expression_to_replace
                    and expression_to_replace_is_in_set.right == set_
                ), f"{expression_to_replace_is_in_set} is not a proof that {expression_to_replace} is in {set_}"
        new_p = exists_cls.from_proposition(
            existential_var_name=existential_var,
            expression_to_replace=expression_to_replace,
            set_=set_,
            latex_name=latex_name,
            inner_proposition=self,
            positions=positions,
            _is_proven=True,
            _inference=Inference(self, rule="thus_there_exists"),
            _assumptions=get_assumptions(self).copy(),
        )

        return new_p

    @overload
    def thus_forall(
        self,
        variable_or_containment: IsContainedIn[Term, Set | Variable | Class],
        **kwargs,
    ) -> ForallInSet[Self]: ...
    @overload
    def thus_forall(
        self,
        variable_or_containment: Variable,
        set_: Set | Variable | Class,
        **kwargs,
    ) -> ForallInSet[Self]: ...
    @overload
    def thus_forall(
        self,
        variable_or_containment: Variable,
        **kwargs,
    ) -> Forall[Self]: ...
    def thus_forall(
        self,
        variable_or_containment: Variable | IsContainedIn[Term, Set | Variable | Class],
        set_: Set | Variable | Class | None = None,
        **kwargs,
    ) -> Forall[Self] | ForallInSet[Self]:
        """
        Given self is proven, return a new proposition that for all variables, self is true.
        This inference rule binds the variable, so you cannot reuse the variable
        unless you unbind it.
        """
        assert self.is_proven, f"{self} is not proven"
        from pylogic.inference import Inference
        from pylogic.proposition.quantified.forall import Forall, ForallInSet
        from pylogic.proposition.relation.contains import IsContainedIn
        from pylogic.variable import Variable

        if isinstance(variable_or_containment, IsContainedIn):
            assert (
                variable_or_containment.is_assumption
            ), f"{variable_or_containment} is not an assumption"
            variable = variable_or_containment.left
            assert isinstance(variable, Variable), f"{variable} is not a variable"
            set_ = variable_or_containment.right
            cls = ForallInSet
            variable_or_containment._set_is_assumption(False)
        else:
            variable = variable_or_containment
            if set_ is not None:
                assert variable in set_, f"{variable} is not in {set_}"
            set_ = set_
            cls = Forall if set_ is None else ForallInSet
        assert variable.is_bound is False, f"{variable} is already bound"
        assert len(variable.depends_on) == 0, f"{variable} depends on something"
        return cls(
            variable=variable,
            set_=set_,  # type:ignore
            inner_proposition=self,
            _is_proven=True,
            _inference=Inference(self, rule="thus_forall"),
            _assumptions=get_assumptions(self).copy(),
            **kwargs,
        )

    def close_all_scopes(self) -> Proposition:
        """
        Close all scopes in the proposition.
        If assumptions (A) were used to deduce this proposition (self), they are
        removed and we get a proof of A -> self.
        If variables exist in the proposition, they are universally quantified.
        Universal quantifiers scopes are closed last so they are outermost.
        """
        from pylogic.expressions.expr import Expr
        from pylogic.variable import Variable

        # TODO: Fix this. Propoition needs to have .symbols, .sets, .functions just like Expr
        # in order for this to work correctly.

        new_p = self.followed_from(*self.from_assumptions)
        all_vars = set()
        for arg in self.args:
            if isinstance(arg, Expr):
                expr_symbols = arg.symbols
                all_vars.update(expr_symbols)
            elif isinstance(arg, Variable):
                all_vars.add(arg)
        for v in all_vars:
            new_p = new_p.thus_forall(v)
        return new_p

    def de_morgan(self) -> Self:
        """
        Apply De Morgan's law to self to return an equivalent proposition.

        In intuitionistic logic, the only valid De Morgan's laws are

        `~A and ~B <-> ~(A or B)`

        `~A or ~B -> ~(A and B)`.
        """
        return self

    def contradicts(self, other: Proposition) -> Contradiction:
        """
        Logical inference rule. If `self` and `other` are negations (and both proven),
        return a contradiction.

        Examples
        --------
        >>> p1 = prop("P").assume()
        >>> p2 = neg(prop("P")).assume()
        >>> p3 = p1.contradicts(p2)
        >>> p3, p3.is_proven
        (contradiction, True)
        """
        assert self.is_proven, f"{self} is not proven"
        assert other.is_proven, f"{other} is not proven"
        from pylogic.inference import Inference
        from pylogic.proposition.contradiction import Contradiction
        from pylogic.proposition.not_ import are_negs

        if are_negs(self, other):
            return Contradiction(
                _is_proven=True,
                _inference=Inference(self, other, rule="contradicts"),
                _assumptions=get_assumptions(self).union(get_assumptions(other)),
            )
        raise ValueError(f"{self} and {other} are not negations")

    def has_as_subproposition(self, other: Proposition) -> bool:
        """
        Check if other is a subproposition of self.
        """
        return self == other

    def unify(self, other: Proposition) -> Unification | Literal[True] | None:
        """
        Algorithm to unify two propositions.
        If unification succeeds, a dictionary of values to instantiate variables
        to is returned.
        The dictionary never instantiates a variable `y` to variable `y`.
        It may instantiate a variable `y` to variable `x` or a variable
        `y` to a symbol or value `y`.
        If no instantiations need to be made (eg propositions are equal),
        return True.
        Otherwise (unification fails), return None.

        Will also unify pylogic.Expr (unevaluated expressions).
        """
        if not isinstance(other, Proposition):
            raise TypeError(f"{other} is not a proposition")
        assert (
            self.is_atomic and other.is_atomic
        ), f"{self} and {other} are not atomic sentences"
        from pylogic.helpers import unify as term_unify

        if self.name != other.name or len(self.args) != len(other.args):
            return None
        d: Unification = {}
        for s_arg, o_arg in zip(self.args, other.args):
            res = term_unify(s_arg, o_arg)
            if isinstance(res, dict):
                for k in res:
                    if k in d and d[k] != res[k]:
                        return None
                    d[k] = res[k]
            elif res is None:
                return None
        if len(d) == 0:
            return True
        else:
            return d


def predicate(name: str) -> Callable[..., Proposition]:
    """
    Create a predicate with a given name.

    A predicate is a python function that returns a proposition.

    When called, the function returns a proposition with the given name and arguments.
    """

    def inner(*args, **kwargs) -> Proposition:
        return Proposition(name, args=args, **kwargs)

    return inner


@overload
def predicates(name: str) -> Callable[..., Proposition]: ...
@overload
def predicates(*names: str) -> tuple[Callable[..., Proposition], ...]: ...
def predicates(  # type: ignore
    *names: str,
) -> Callable[..., Proposition] | tuple[Callable[..., Proposition], ...]:
    """
    Create multiple predicates with the given names.
    """
    if len(names) == 1:
        return predicate(names[0])
    return tuple(predicate(name) for name in names)


pred = predicate
preds = predicates


def proposition(name: str, *args: Term, **kwargs) -> Proposition:
    """
    Create a proposition with a given name and arguments.
    """
    return Proposition(name, args=args, **kwargs)


@overload
def propositions(name: str, args: tuple[Term, ...] = (), **kwargs) -> Proposition: ...
@overload
def propositions(
    *names: str, args: tuple[Term, ...] = (), **kwargs
) -> tuple[Proposition, ...]: ...
def propositions(  # type: ignore
    *names: str, args: tuple[Term, ...] = (), **kwargs
) -> Proposition | tuple[Proposition, ...]:
    """
    Create multiple propositions with the given names.
    """
    if len(names) == 1:
        return proposition(names[0], *args, **kwargs)
    return tuple(proposition(name, *args, **kwargs) for name in names)


prop = proposition
props = propositions

if __name__ == "__main__":
    pass
