from __future__ import annotations

from typing import TYPE_CHECKING, Any, Callable, Self, TypeVar, cast

import sympy as sp

from pylogic.enviroment_settings.settings import settings
from pylogic.expressions.expr import Add, Expr, Mul, Pow
from pylogic.typing import PythonNumeric, Term

if TYPE_CHECKING:
    from pylogic.expressions.abs import Abs
    from pylogic.expressions.sequence_term import SequenceTerm
    from pylogic.proposition.not_ import Not
    from pylogic.proposition.ordering.greaterorequal import GreaterOrEqual
    from pylogic.proposition.ordering.greaterthan import GreaterThan
    from pylogic.proposition.ordering.lessorequal import LessOrEqual
    from pylogic.proposition.ordering.lessthan import LessThan
    from pylogic.proposition.proposition import Proposition
    from pylogic.proposition.relation.contains import IsContainedIn
    from pylogic.proposition.relation.equals import Equals
    from pylogic.proposition.relation.subsets import IsSubsetOf
    from pylogic.structures.class_ import Class
    from pylogic.structures.set_ import Set
    from pylogic.sympy_helpers import PylSympySymbol
    from pylogic.variable import Variable

    S = TypeVar("S", bound=Set)
else:
    S = TypeVar("S")


class Symbol:
    is_atomic = True

    # list of attributes not listed in kwargs that can change during the
    # lifetime of this symbol,
    # that need to be copied when a copy is made
    mutable_attrs_to_copy = [
        "properties_of_each_term",
        "independent_dependencies",
    ]
    # names of keyword arguments that can be passed to the constructor
    # to attribute names
    # "dummy" means that there is no corresponding attribute
    kwargs = [
        ("name", "name"),
        ("_from_existential_instance", "_from_existential_instance"),
        ("knowledge_base", "knowledge_base"),
        ("real", "_is_real"),
        ("rational", "_is_rational"),
        ("integer", "_is_integer"),
        ("natural", "_is_natural"),
        ("zero", "_is_zero"),
        ("nonpositive", "_is_nonpositive"),
        ("nonnegative", "_is_nonnegative"),
        ("even", "_is_even"),
        ("sequence", "_is_sequence"),
        ("finite", "_is_finite"),
        ("length", "length"),
        ("positive", "dummy"),
        ("negative", "dummy"),
        ("set_", "_is_set"),
        ("graph", "is_graph"),
        ("pair", "is_pair"),
        ("list_", "is_list_"),
        ("latex_name", "latex_name"),
        ("depends_on", "depends_on"),
        ("sets_contained_in", "sets_contained_in"),
    ]

    def __init__(self, *args, **kwargs) -> None:
        """
        Represents a symbolic object. Can be a Variable or a Constant.
        """
        # _internal only: used when copying a symbol
        _is_copy = kwargs.get("_is_copy", False)
        if _is_copy:
            assert len(args) == 0, "Symbol copy should not have positional arguments"
            self.__copy_init__(**kwargs)
        else:
            self.__new_init__(*args, **kwargs)

    def __copy_init__(self, **kwargs) -> None:
        # these attrs are not copied
        self.parent_exprs = []

        self.__dict__.update(kwargs)
        self._init_args = ()
        self._init_kwargs = kwargs

    def __new_init__(self, *args, **kwargs) -> None:
        from pylogic.helpers import _add_assumption_props

        name = args[0]
        assert isinstance(name, str), "The first argument must be a string"
        self.knowledge_base: set[Proposition] = kwargs.get("knowledge_base", set())
        self.name: str = name
        self._is_real: bool | None = kwargs.get("real", None)
        self._is_rational: bool | None = kwargs.get("rational", None)
        self._is_integer: bool | None = kwargs.get("integer", None)
        self._is_natural: bool | None = kwargs.get("natural", None)

        self._is_zero: bool | None = kwargs.get("zero", None)
        self._is_nonpositive: bool | None = kwargs.get("nonpositive", None)
        self._is_nonnegative: bool | None = kwargs.get("nonnegative", None)
        self._is_even: bool | None = kwargs.get("even", None)

        self._is_set: bool | None = kwargs.get("set_", None)
        self.is_graph: bool | None = not self.is_set and kwargs.get("graph", None)
        self.is_pair: bool | None = self.is_graph or kwargs.get("pair", None)
        self.is_list_: bool | None = self.is_pair or kwargs.get("list_", None)

        # sequences, finite
        self._is_sequence: bool | None = self.is_list or kwargs.get("sequence", None)
        self._is_finite: bool | None = kwargs.get("finite", None)

        # list of expressions that contain this symbol
        # not copied
        self.parent_exprs: list[Expr] = []
        self.length: Term | None = kwargs.get("length", None)

        self._init_args = args
        self._init_kwargs = kwargs
        self._from_existential_instance = kwargs.get(
            "_from_existential_instance", False
        )
        self.latex_name = (
            kwargs.get("latex_name") or self.name
        )  # using "or" instead of default here because latex_name=None is valid

        self.depends_on: tuple[Symbol, ...] = kwargs.get("depends_on", ())
        self.independent_dependencies = self.get_independent_dependencies()
        self.sets_contained_in: set[Set] = kwargs.get("sets_contained_in", set())

        # for variable sequences&sets
        self.properties_of_each_term: list[Proposition] = []
        _add_assumption_props(self, kwargs)

        self._is_copy = False

    @property
    def is_natural(self) -> bool | None:
        from pylogic.helpers import ternary_and, ternary_or

        return ternary_or(
            self._is_natural, ternary_and(self._is_integer, self._is_nonnegative)
        )

    @is_natural.setter
    def is_natural(self, value: bool | None):
        self._is_natural = value
        for parent in self.parent_exprs:
            parent.update_properties()

    @property
    def is_integer(self) -> bool | None:
        from pylogic.helpers import ternary_or

        return ternary_or(self._is_integer, self._is_natural)

    @is_integer.setter
    def is_integer(self, value: bool | None):
        self._is_integer = value
        for parent in self.parent_exprs:
            parent.update_properties()

    @property
    def is_rational(self) -> bool | None:
        return self._is_rational or self.is_integer

    @is_rational.setter
    def is_rational(self, value: bool | None):
        self._is_rational = value
        for parent in self.parent_exprs:
            parent.update_properties()

    @property
    def is_real(self) -> bool | None:
        return self._is_real or self.is_rational

    @is_real.setter
    def is_real(self, value: bool | None):
        self._is_real = value
        for parent in self.parent_exprs:
            parent.update_properties()

    @property
    def is_zero(self) -> bool | None:
        return self._is_zero

    @is_zero.setter
    def is_zero(self, value: bool | None):
        self._is_zero = value
        for parent in self.parent_exprs:
            parent.update_properties()

    @property
    def is_nonzero(self) -> bool | None:
        from pylogic.helpers import ternary_not

        return ternary_not(self.is_zero)

    @property
    def is_even(self) -> bool | None:
        return self._is_even

    @is_even.setter
    def is_even(self, value: bool | None):
        self._is_even = value
        for parent in self.parent_exprs:
            parent.update_properties()

    @property
    def is_odd(self) -> bool | None:
        from pylogic.helpers import ternary_not

        return ternary_not(self.is_even)

    @property
    def is_positive(self) -> bool | None:
        from pylogic.helpers import ternary_and

        return ternary_and(self.is_nonnegative, self.is_nonzero)

    @property
    def is_negative(self) -> bool | None:
        from pylogic.helpers import ternary_and

        return ternary_and(self.is_nonpositive, self.is_nonzero)

    @property
    def is_nonpositive(self) -> bool | None:
        return self._is_nonpositive

    @is_nonpositive.setter
    def is_nonpositive(self, value: bool | None):
        self._is_nonpositive = value
        for parent in self.parent_exprs:
            parent.update_properties()

    @property
    def is_nonnegative(self) -> bool | None:
        from pylogic.helpers import ternary_or

        return ternary_or(self._is_nonnegative, self._is_natural)

    @is_nonnegative.setter
    def is_nonnegative(self, value: bool | None):
        self._is_nonnegative = value
        for parent in self.parent_exprs:
            parent.update_properties()

    @property
    def is_set(self) -> bool | None:
        return self._is_set

    @is_set.setter
    def is_set(self, value: bool | None):
        self._is_set = value
        for parent in self.parent_exprs:
            parent.update_properties()

    @property
    def is_list(self) -> bool | None:
        return self.is_list_

    @property
    def is_sequence(self) -> bool | None:
        return self._is_sequence

    @is_sequence.setter
    def is_sequence(self, value: bool | None):
        self._is_sequence = value
        # parent expressions don't currently depend
        # on this property
        # for parent in self.parent_exprs:
        #     parent.update_properties()

    @property
    def is_finite(self) -> bool | None:
        return self._is_finite

    @is_finite.setter
    def is_finite(self, value: bool | None):
        self._is_finite = value
        # parent expressions don't currently depend
        # on this property
        # for parent in self.parent_exprs:
        #     parent.update_properties()

    def __repr__(self):
        return f"{self.__class__.__name__}({self.name}, deps={self.depends_on})"

    def __str__(self):
        name_part = self.name
        if self.is_sequence:
            name_part += "_n"
        if len(self.independent_dependencies) > 0 and settings["SHOW_VARIABLE_DEPS"]:
            return f"{name_part}({', '.join(str(d) for d in self.independent_dependencies)})"
        return f"{name_part}"

    def __add__(self, other: Symbol | PythonNumeric | Expr) -> Add:
        return Add(self, other)

    def __sub__(self, other: Symbol | PythonNumeric | Expr) -> Add:
        o = cast(Mul | PythonNumeric, -other)
        return Add(self, o)

    def __mul__(self, other: Symbol | PythonNumeric | Expr) -> Mul:
        return Mul(self, other)

    def __truediv__(self, other: Symbol | PythonNumeric | Expr) -> Pow | Mul:
        if self == 1:
            return Pow(other, -1)
        return Mul(self, Pow(other, -1))

    def __neg__(self) -> Mul:
        val = Mul(-1, self)
        return val

    def __pow__(self, other: Symbol | PythonNumeric | Expr) -> Pow:
        return Pow(self, other)

    def __radd__(self, other: Symbol | PythonNumeric | Expr) -> Add:
        return Add(other, self)

    def __rsub__(self, other: Symbol | PythonNumeric | Expr) -> Add:
        return Add(other, -self)

    def __rmul__(self, other: Symbol | PythonNumeric | Expr) -> Mul:
        return Mul(other, self)

    def __rtruediv__(self, other: Symbol | PythonNumeric | Expr) -> Mul | Pow:
        if other == 1:
            return Pow(self, -1)
        return Mul(other, Pow(self, -1))

    def __abs__(self) -> Abs:
        from pylogic.expressions.abs import Abs

        return Abs(self)

    def __rpow__(self, other: Symbol | PythonNumeric | Expr) -> Pow:
        return Pow(other, self)

    def __mod__(self, modulus: Symbol | PythonNumeric | Expr) -> Mod:
        from pylogic.expressions.mod import Mod

        return Mod(self, modulus)

    def __rmod__(self, modulus: Symbol | PythonNumeric | Expr) -> Mod:
        from pylogic.expressions.mod import Mod

        return Mod(modulus, self)

    def __eq__(self, other: Any) -> bool:
        """
        Check if two symbols are structurally equal.
        """
        if self is other:
            return True
        if isinstance(other, Symbol):
            return (
                self.name == other.name
                and self.__class__ == other.__class__
                and self.is_real == other.is_real
                and self.is_set == other.is_set
                # and self.is_graph == other.is_graph
                # and self.is_pair == other.is_pair
                # and self.is_list_ == other.is_list_
                and self.is_sequence == other.is_sequence
                and self.depends_on == other.depends_on
            )

        return NotImplemented

    def __lt__(self, other: Any) -> bool | LessThan:
        from pylogic.proposition.ordering.lessthan import LessThan

        if settings["PYTHON_OPS_RETURN_PROPS"]:
            return LessThan(self, other)
        return NotImplemented

    def __le__(self, other: Any) -> bool | LessOrEqual:
        from pylogic.proposition.ordering.lessorequal import LessOrEqual

        if settings["PYTHON_OPS_RETURN_PROPS"]:
            return LessOrEqual(self, other)
        return NotImplemented

    def __gt__(self, other: Any) -> bool | GreaterThan:
        from pylogic.proposition.ordering.greaterthan import GreaterThan

        if settings["PYTHON_OPS_RETURN_PROPS"]:
            return GreaterThan(self, other)
        return NotImplemented

    def __ge__(self, other: Any) -> bool | GreaterOrEqual:
        from pylogic.proposition.ordering.greaterorequal import GreaterOrEqual

        if settings["PYTHON_OPS_RETURN_PROPS"]:
            return GreaterOrEqual(self, other)
        return NotImplemented

    def eval_same(self, other: Any) -> bool:
        """
        Check if two symbols evaluate to the same value.
        """
        if isinstance(other, Symbol):
            return self.evaluate() == other.evaluate()
        return self.evaluate() == other

    def get_independent_dependencies(self) -> tuple[Variable, ...]:
        indeps = []
        for dep in self.depends_on:
            if len(dep.depends_on) == 0:
                indeps.append(dep)
            else:
                indeps.extend(dep.get_independent_dependencies())
        return tuple(indeps)

    def equals(self, other: Symbol | PythonNumeric | Expr | Set, **kwargs) -> Equals:
        from pylogic.proposition.relation.equals import Equals

        return Equals(self, other, **kwargs)

    def is_subset_of(self, other: Symbol | Set, **kwargs) -> IsSubsetOf:
        from pylogic.proposition.relation.subsets import IsSubsetOf

        return IsSubsetOf(self, other, **kwargs)  # type: ignore

    def _latex(self) -> str:
        if self.is_sequence:
            return f"{self.latex_name}_n"
        return self.latex_name

    def _repr_latex_(self) -> str:
        return f"$${self._latex()}$$"

    def copy(self) -> Self:
        """
        Create a copy of this symbol.
        """
        kw = {k: getattr(self, k, None) for k in self.mutable_attrs_to_copy}
        kw.update(
            {val: getattr(self, val, None) for _, val in self.kwargs if val != "dummy"}
        )
        return self.__class__(_is_copy=True, **kw)

    def deepcopy(self) -> Self:
        return self.copy()

    def replace(
        self,
        replace_dict: dict,
        equal_check: Callable | None = None,
        positions: list[list[int]] | None = None,
    ) -> Any:
        """
        Replace occurences of `old` with `new` in the object, where replace_dict = {old: new}.
        If `equal_check` is provided, it should be a function that takes two
        arguments and returns True if they are equal.
        """
        equal_check = equal_check or (lambda x, y: x == y)
        for old, new in replace_dict.items():
            if equal_check(old, self):
                return new
        return self

    def to_sympy(self) -> sp.Symbol:
        from pylogic.sympy_helpers import PylSympySymbol

        kw = {k: getattr(self, k, None) for k in self.mutable_attrs_to_copy}
        kw.update(
            {val: getattr(self, val, None) for _, val in self.kwargs if val != "dummy"}
        )
        kw["_is_copy"] = True

        symbol_kwargs = (
            self._init_kwargs
            if not self._is_copy
            else {
                kwarg: getattr(self, val)
                for kwarg, val in self.kwargs
                if val != "dummy"
            }
        )

        return PylSympySymbol(
            *self._init_args,  # TODO: _init_args are different for copy
            _pyl_class=self.__class__,
            _pyl_init_args=(),
            _pyl_init_kwargs=kw,
            **symbol_kwargs,
        )

    def _sympy_(self) -> sp.Symbol:
        # for sympy internal use
        return self.to_sympy()

    def evaluate(self, **kwargs) -> Self:
        return self

    def is_in(
        self, other: Set | Variable | Class | SequenceTerm[S], **kwargs
    ) -> IsContainedIn:
        from pylogic.proposition.relation.contains import IsContainedIn

        return IsContainedIn(self, other, **kwargs)

    def is_not_in(
        self, other: Set | Variable | Class | SequenceTerm[S], **kwargs
    ) -> Not[IsContainedIn]:
        from pylogic.proposition.not_ import Not

        return Not(self.is_in(other), **kwargs)

    def _is_in_by_rule(
        self, other: Set | Class | Variable, rule: str = "by_definition"
    ) -> IsContainedIn:
        from pylogic.inference import Inference
        from pylogic.proposition.relation.contains import IsContainedIn

        res = IsContainedIn(
            self,
            other,
            _is_proven=True,
            _assumptions=set(),
            _inference=Inference(None, rule=rule),
        )
        return res

    def contains(self, other: Term, **kwargs) -> IsContainedIn:
        from pylogic.proposition.relation.contains import IsContainedIn

        return IsContainedIn(other, self, **kwargs)

    @property
    def nodes_edges(self) -> tuple[Self, Self]:
        """
        if self has `is_graph` True, return two variables representing the nodes
        and edges of self. Otherwise, raise a ValueError
        """
        if self.is_graph:
            return self.__class__(f"{self.name}_{{nodes}}", set_=True), self.__class__(
                f"{self.name}_{{edges}}", set_=True
            )
        raise ValueError(f"{self} is not a graph")

    @property
    def first_second(self) -> tuple[Self, Self]:
        """
        if self has `is_pair` True, return two variables representing the first
        and second elements of self. Otherwise, raise a ValueError
        """
        if self.is_pair:
            return self.__class__(f"{self.name}_{{first}}"), self.__class__(
                f"{self.name}_{{second}}"
            )
        raise ValueError(f"{self} is not a pair")

    @property
    def size(self) -> Self | sp.Integer:
        """
        if self has `is_list` or `is_set` True, return a variable representing the
        size of self. Otherwise, raise a ValueError.
        Note that a graph is a pair, which is a list of two elements, so it
        has a size. This size, however, is 2.
        To get the number of nodes, access `self.nodes_edges[0].size`.
        """
        if self.is_list or self.is_set:
            return self.__class__(f"size({self.name})", nonnegative=True, integer=True)
        elif self.is_pair:
            return sp.Integer(2)
        raise ValueError(f"{self} is not a list or a set")

    def __hash__(self):
        return hash(
            (
                self.__class__.__name__,
                self.name,
                self.is_real,
                self.is_set,
                self.is_sequence,
            )
        )


def symbols(*args, **kwargs):
    return sp.symbols(*args, cls=Symbol, **kwargs)
