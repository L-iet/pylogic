from __future__ import annotations
from typing import Any, Self, cast
from fractions import Fraction

from pylogic.expressions.expr import Expr, Add, Mul, Pow

import sympy as sp
from sympy.matrices.expressions.matexpr import MatrixElement as MatEl

Numeric = Fraction | int | float


class Symbol:
    def __init__(self, *args, **kwargs) -> None:
        assert isinstance(args[0], str), "The first argument must be a string"
        self.name: str = args[0]
        self.is_real: bool = kwargs.get("real", False)
        self.is_set_: bool = kwargs.get("set_", False)
        self.is_set: bool = self.is_set_
        self.is_graph: bool = not self.is_set and kwargs.get("graph", False)
        self.is_pair: bool = self.is_graph or kwargs.get("pair", False)
        self.is_list_: bool = self.is_pair or kwargs.get("list_", False)
        self.is_list: bool = self.is_list_
        self.is_sequence: bool = self.is_list or kwargs.get("sequence", False)
        self._init_args = args
        self._init_kwargs = kwargs

    def __repr__(self):
        return self.name

    def __add__(self, other: Symbol | Numeric | Expr) -> Add:
        return Add(self, other)

    def __sub__(self, other: Symbol | Numeric | Expr) -> Add:
        o = cast(Mul | Numeric, -other)
        return Add(self, o)

    def __mul__(self, other: Symbol | Numeric | Expr) -> Mul:
        return Mul(self, other)

    def __truediv__(self, other: Symbol | Numeric | Expr) -> Mul:
        return Mul(self, Pow(other, -1))

    def __neg__(self) -> Mul:
        return Mul(-1, self)

    def __pow__(self, other: Symbol | Numeric | Expr) -> Pow:
        return Pow(self, other)

    def __radd__(self, other: Symbol | Numeric | Expr) -> Add:
        return Add(other, self)

    def __rsub__(self, other: Symbol | Numeric | Expr) -> Add:
        return Add(other, -self)

    def __rmul__(self, other: Symbol | Numeric | Expr) -> Mul:
        return Mul(other, self)

    def __rtruediv__(self, other: Symbol | Numeric | Expr) -> Mul:
        return Mul(other, Pow(self, -1))

    def __rpow__(self, other: Symbol | Numeric | Expr) -> Pow:
        return Pow(other, self)

    def _latex(self) -> str:
        return self.name

    def _repr_latex_(self) -> str:
        return f"$${self._latex()}$$"

    def copy(self) -> Self:
        return self.__class__(self.name)

    def replace(self, old, new) -> Any:
        if self == old:
            return new
        return self

    def evaluate(self) -> sp.Basic:
        return sp.Symbol(*self._init_args, **self._init_kwargs)

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
        return MatAdd(self, other)

    def __mul__(self, other) -> MatMul:
        return MatMul(self, other)

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
        return MatMul(self, other)

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
