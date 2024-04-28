from __future__ import annotations
import sympy as sp


class Variable(sp.Symbol):
    def __init__(self, *args, **kwargs) -> None:
        super().__init__(*args, **kwargs)
        self.is_set_: bool = kwargs.get("set_", False)
        self.is_set: bool = self.is_set_
        self.is_graph: bool = kwargs.get("graph", False)
        self.is_pair: bool = kwargs.get("pair", False)
        self.is_list_: bool = kwargs.get("list_", False)
        self.is_list: bool = self.is_list_

    def __repr__(self):
        return super().__repr__()

    def copy(self) -> Variable:
        return Variable(self.name)

    def vertices_edges(self) -> tuple[Variable, Variable]:
        """
        if self has `is_graph` True, return two variables representing the nodes
        and edges of self. Otherwise, raise a ValueError
        """
        if self.is_graph:
            return Variable(f"{self.name}_{{nodes}}", set_=True), Variable(
                f"{self.name}_{{edges}}", set_=True
            )
        raise ValueError(f"{self} is not a graph")

    def size(self) -> Variable:
        """
        if self has `is_list` or `is_set` True, return a variable representing the
        size of self. Otherwise, raise a ValueError
        """
        if self.is_list or self.is_set:
            return Variable(f"size({self.name})", positive=True, integer=True)
        raise ValueError(f"{self} is not a list or a set")


Var = Variable
