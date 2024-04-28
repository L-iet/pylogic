from __future__ import annotations
from typing import Self
import sympy as sp

MatEl = sp.matrices.expressions.matexpr.MatrixElement


class Symbol(sp.Symbol):
    def __init__(self, *args, **kwargs) -> None:
        super().__init__()
        self.is_set_: bool = kwargs.get("set_", False)
        self.is_set: bool = self.is_set_
        self.is_graph: bool = kwargs.get("graph", False)
        self.is_pair: bool = kwargs.get("pair", False)
        self.is_list_: bool = kwargs.get("list_", False)
        self.is_list: bool = self.is_list_

    def __repr__(self):
        return super().__repr__()

    def copy(self) -> Self:
        return self.__class__(self.name)

    def vertices_edges(self) -> tuple[Self, Self]:
        """
        if self has `is_graph` True, return two variables representing the nodes
        and edges of self. Otherwise, raise a ValueError
        """
        if self.is_graph:
            return self.__class__(f"{self.name}_{{nodes}}", set_=True), self.__class__(
                f"{self.name}_{{edges}}", set_=True
            )
        raise ValueError(f"{self} is not a graph")

    def size(self) -> Self:
        """
        if self has `is_list` or `is_set` True, return a variable representing the
        size of self. Otherwise, raise a ValueError
        """
        if self.is_list or self.is_set:
            return self.__class__(f"size({self.name})", positive=True, integer=True)
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
