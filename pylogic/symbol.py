from __future__ import annotations
from typing import Any, Self
from fractions import Fraction

from pylogic.expressions.expr import Expr, Add, Mul, Pow

import sympy as sp
from sympy.matrices.expressions.matexpr import MatrixElement as MatEl

Numeric = Fraction | int | float


class Symbol(sp.Symbol):
    def __init__(self, *args, **kwargs) -> None:
        super().__init__()
        self.is_set_: bool = kwargs.get("set_", False)
        self.is_set: bool = self.is_set_
        self.is_graph: bool = not self.is_set and kwargs.get("graph", False)
        self.is_pair: bool = self.is_graph or kwargs.get("pair", False)
        self.is_list_: bool = self.is_pair or kwargs.get("list_", False)
        self.is_list: bool = self.is_list_
        self.is_sequence: bool = self.is_list or kwargs.get("sequence", False)

    def __repr__(self):
        return super().__repr__()

    def __add__(self, other: Symbol | Numeric | Expr) -> sp.Add:
        return Add(self, other).evaluate()

    def __sub__(self, other: Symbol | Numeric | Expr) -> sp.Add:
        return Add(self, -other).evaluate()

    def __mul__(self, other: Symbol | Numeric | Expr) -> sp.Mul:
        return Mul(self, other).evaluate()

    def __truediv__(self, other: Symbol | Numeric | Expr) -> sp.Mul:
        return Mul(self, Pow(other, -1)).evaluate()

    def __neg__(self) -> sp.Mul:
        return Mul(-1, self).evaluate()

    def __pow__(self, other: Symbol | Numeric | Expr) -> sp.Pow:
        return Pow(self, other).evaluate()

    def __radd__(self, other: Symbol | Numeric | Expr) -> sp.Add:
        return Add(other, self).evaluate()

    def __rsub__(self, other: Symbol | Numeric | Expr) -> sp.Add:
        return Add(other, -self).evaluate()

    def __rmul__(self, other: Symbol | Numeric | Expr) -> sp.Mul:
        return Mul(other, self).evaluate()

    def __rtruediv__(self, other: Symbol | Numeric | Expr) -> sp.Mul:
        return Mul(other, Pow(self, -1)).evaluate()

    def __rpow__(self, other: Symbol | Numeric | Expr) -> sp.Pow:
        return Pow(other, self).evaluate()

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

    __hash__ = sp.Symbol.__hash__


class Function(sp.Function):
    def __repr__(self):
        return super().__repr__()


class MatrixSymbol(sp.MatrixSymbol):
    def __repr__(self):
        return super().__repr__()

    def __add__(self, other) -> "MatAdd":
        return MatAdd(self, other)

    def __mul__(self, other) -> "MatMul":
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

    def __mul__(self, other) -> "MatMul":
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
