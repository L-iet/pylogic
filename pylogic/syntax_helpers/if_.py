from __future__ import annotations

from typing import TYPE_CHECKING, Callable, Generic, TypeVar, overload

from pylogic.expressions.expr import Expr
from pylogic.proposition.implies import Implies
from pylogic.typing import Term

if TYPE_CHECKING:
    from pylogic.expressions.function import PiecewiseBranch
    from pylogic.proposition.proposition import Proposition

    P = TypeVar("P", bound=Proposition)
    Q = TypeVar("Q", bound=Proposition)
    R = TypeVar("R", bound=Proposition)
    E = TypeVar("E", bound=Expr)
else:
    P = TypeVar("P")
    Q = TypeVar("Q")
    R = TypeVar("R")
    E = TypeVar("E")


class _If(Generic[P]):
    def __init__(self, condition: P) -> None:
        self.condition: P = condition

    @overload
    def then(
        self, then_statement: Expr | Callable[..., Term], **kwargs
    ) -> PiecewiseBranch[P]: ...
    @overload
    def then(self, then_statement: Q, **kwargs) -> Implies[P, Q]: ...
    def then(
        self, then_statement: Q | Expr | Callable[..., Term], **kwargs
    ) -> Implies[P, Q] | PiecewiseBranch[P]:
        from pylogic.proposition.proposition import Proposition

        if not isinstance(then_statement, Proposition):
            return PiecewiseBranch(self.condition, then_statement, **kwargs)
        return Implies(self.condition, then_statement, **kwargs)


def if_(condition: P) -> _If[P]:
    return _If(condition)


If = if_
