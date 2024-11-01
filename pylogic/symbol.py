from __future__ import annotations

from typing import TYPE_CHECKING, Any, Callable, Self, TypeVar, cast

import sympy as sp
from sympy.matrices.expressions.matexpr import MatrixElement as MatEl

from pylogic import PythonNumeric, Term
from pylogic.expressions.expr import Add, Expr, Mul, Pow

if TYPE_CHECKING:
    from pylogic.expressions.sequence_term import SequenceTerm
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
    def __init__(self, *args, **kwargs) -> None:
        assert isinstance(args[0], str), "The first argument must be a string"
        self.knowledge_base: set[Proposition] = set()
        self.name: str = args[0]
        self._is_real: bool = kwargs.get("real", None)
        self._is_rational: bool = kwargs.get("rational", None)
        self._is_integer: bool = kwargs.get("integer", None)
        self._is_natural: bool = kwargs.get("natural", None)
        self.is_set_: bool = kwargs.get("set_", None)
        self.is_set: bool = self.is_set_
        self.is_graph: bool = not self.is_set and kwargs.get("graph", None)
        self.is_pair: bool = self.is_graph or kwargs.get("pair", None)
        self.is_list_: bool = self.is_pair or kwargs.get("list_", None)
        self.is_list: bool = self.is_list_
        self.is_sequence: bool = self.is_list or kwargs.get("sequence", None)
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

    @property
    def is_natural(self) -> bool:
        return self._is_natural

    @property
    def is_integer(self) -> bool:
        return self._is_integer or self.is_natural

    @property
    def is_rational(self) -> bool:
        return self._is_rational or self.is_integer

    @property
    def is_real(self) -> bool:
        return self._is_real or self.is_rational

    def __repr__(self):
        return f"{self.__class__.__name__}({self.name}, deps={self.depends_on})"

    def __str__(self):
        from pylogic.enviroment_settings.settings import VIEW_VARIABLE_DEPS

        if len(self.independent_dependencies) > 0 and VIEW_VARIABLE_DEPS:
            return f"{self.name}({', '.join(str(d) for d in self.independent_dependencies)})"
        return f"{self.name}"

    def __add__(self, other: Symbol | PythonNumeric | Expr) -> Add:
        return Add(self, other)

    def __sub__(self, other: Symbol | PythonNumeric | Expr) -> Add:
        o = cast(Mul | PythonNumeric, -other)
        return Add(self, o)

    def __mul__(self, other: Symbol | PythonNumeric | Expr) -> Mul:
        return Mul(self, other)

    def __truediv__(self, other: Symbol | PythonNumeric | Expr) -> Mul:
        return Mul(self, Pow(other, -1))

    def __neg__(self) -> Mul:
        return Mul(-1, self)

    def __pow__(self, other: Symbol | PythonNumeric | Expr) -> Pow:
        return Pow(self, other)

    def __radd__(self, other: Symbol | PythonNumeric | Expr) -> Add:
        return Add(other, self)

    def __rsub__(self, other: Symbol | PythonNumeric | Expr) -> Add:
        return Add(other, -self)

    def __rmul__(self, other: Symbol | PythonNumeric | Expr) -> Mul:
        return Mul(other, self)

    def __rtruediv__(self, other: Symbol | PythonNumeric | Expr) -> Mul:
        return Mul(other, Pow(self, -1))

    def __rpow__(self, other: Symbol | PythonNumeric | Expr) -> Pow:
        return Pow(other, self)

    def __eq__(self, other: Any) -> bool:
        """
        Check if two symbols are structurally equal.
        """
        if self is other:
            return True
        if isinstance(other, Symbol):
            return (not self._from_existential_instance) and (
                self.name == other.name
                # TODO: fix replace not working well
                # and self.__class__ == other.__class__
                # and self.is_real == other.is_real
                # and self.is_set_ == other.is_set_
                # and self.is_graph == other.is_graph
                # and self.is_pair == other.is_pair
                # and self.is_list_ == other.is_list_
                # and self.is_sequence == other.is_sequence
                and self.depends_on == other.depends_on
            )
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
        return self.latex_name

    def _repr_latex_(self) -> str:
        return f"$${self._latex()}$$"

    def copy(self) -> Self:
        return self.__class__(*self._init_args, **self._init_kwargs)

    def deepcopy(self) -> Self:
        return self.copy()

    def replace(self, replace_dict: dict, equal_check: Callable | None = None) -> Any:
        """
        Replace occurences of `old` with `new` in the object, where replace_dict = {old: new}.
        If `equal_check` is provided, it should be a function that takes two
        arguments and returns True if they are equal.
        """
        equal_check = equal_check or (lambda x, y: x == y)
        old, new = replace_dict.popitem()
        if equal_check(old, self):
            return new
        return self

    def to_sympy(self) -> PylSympySymbol:
        from pylogic.sympy_helpers import PylSympySymbol

        return PylSympySymbol(
            *self._init_args,
            _pyl_class=self.__class__.__name__,
            _pyl_init_args=self._init_args,
            _pyl_init_kwargs=self._init_kwargs,
            **self._init_kwargs,
        )

    def evaluate(self) -> Self:
        return self

    def is_in(
        self, other: Set | Variable | Class | SequenceTerm[S], **kwargs
    ) -> IsContainedIn:
        from pylogic.proposition.relation.contains import IsContainedIn

        return IsContainedIn(self, other, **kwargs)

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
                self.is_set_,
                self.is_graph,
                self.is_pair,
                self.is_list_,
                self.is_sequence,
            )
        )


class Function(sp.Function):
    def __repr__(self):
        return super().__repr__()


class MatrixSymbol(sp.MatrixSymbol):
    def __repr__(self):
        return super().__repr__()

    def __add__(self, other) -> MatAdd:
        return MatAdd(self, other)  # type: ignore

    def __mul__(self, other) -> MatMul:
        return MatMul(self, other)  # type: ignore

    def transpose(self):
        return Transpose(self)

    @property
    def T(self):
        return self.transpose()


class MatAdd(sp.MatAdd):
    def __repr__(self):
        return super().__repr__()

    def transpose(self, doit=False):
        _t = Transpose(self)
        return _t if not doit else _t.doit(deep=False)

    def __getitem__(self, key):
        return MatrixElement(self, *key)

    @property
    def T(self):
        return self.transpose()


class MatMul(sp.MatMul):
    def __repr__(self):
        return super().__repr__()

    def transpose(self, doit=False):
        _t = Transpose(self)
        return _t if not doit else _t.doit(deep=False)

    def __getitem__(self, key):
        return MatrixElement(self, *key)

    @property
    def T(self):
        return self.transpose()


class MatrixElement(MatEl):
    def __repr__(self):
        return super().__repr__()


class Transpose(sp.Transpose):
    def __repr__(self):
        return super().__repr__()

    def __mul__(self, other) -> MatMul:
        return MatMul(self, other)  # type: ignore

    def __getitem__(self, key):
        return MatrixElement(self, *key)

    def transpose(self, doit=True):
        _t = Transpose(self)
        return _t if not doit else _t.doit(deep=False)

    @property
    def T(self):
        return self.transpose()


def symbols(*args, **kwargs):
    return sp.symbols(*args, cls=Symbol, **kwargs)
