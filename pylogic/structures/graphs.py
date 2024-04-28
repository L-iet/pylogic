from __future__ import annotations
from typing import TYPE_CHECKING

from pylogic.structures.sets import Graphs
from pylogic.variable import Variable
from pylogic.symbol import Symbol

if TYPE_CHECKING:
    from pylogic.structures.sets import Set
    from pylogic.proposition.relation.contains import IsContainedIn
    from sympy import Basic

    Term = Symbol | Set | Basic | int | float


def vertices_edges(
    obj_is_graph: IsContainedIn,
) -> tuple[Variable | Symbol, Variable | Symbol]:
    """
    Given a proof of the form `x in Graphs`, where x is a variable (or symbol),
    return two variables (or symbols) representing the nodes and edges of x
    respectively.
    """
    assert obj_is_graph.is_proven, f"{obj_is_graph} is not proven"
    assert (
        obj_is_graph.set_ == Graphs
    ), f"{obj_is_graph} is not a statement involving set Graphs"
    obj = obj_is_graph.element
    if isinstance(obj, Variable):
        cls = Variable
    else:
        cls = Symbol
    if hasattr(obj, "name"):
        name = obj.name  # type:ignore
    else:
        name = str(obj)

    return (
        cls(rf"{name}_{{nodes}}", set_=True),
        cls(rf"{name}_{{edges}}", set_=True),
    )
