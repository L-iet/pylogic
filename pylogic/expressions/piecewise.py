from __future__ import annotations

from typing import (
    TYPE_CHECKING,
    Generic,
    TypeVar,
    TypeVarTuple,
)

import sympy as sp

from pylogic import Term
from pylogic.expressions.expr import Expr

if TYPE_CHECKING:
    from pylogic.proposition.proposition import Proposition

    P = TypeVar("P", bound=Proposition)
    E = TypeVar("E", bound=Expr)
else:
    P = TypeVar("P")
    E = TypeVar("E")
Ps = TypeVarTuple("Ps")
T = TypeVar("T", bound=Term)


class PiecewiseExpr(Expr, Generic[*Ps]):
    def __init__(
        self, *branches: *Ps, otherwise: Expr | None = None, name: str | None = None
    ) -> None:
        from pylogic.proposition.and_ import And
        from pylogic.proposition.exor import ExOr
        from pylogic.proposition.not_ import neg
        from pylogic.proposition.or_ import Or

        self.branches = None  # type: ignore

        self.name = name
        super().__init__(*branches)  # type: ignore
        self.otherwise_branch: OtherwiseBranch | None = None
        for branch in branches:
            if self.otherwise_branch is not None:
                raise ValueError(
                    "Only one otherwise branch is allowed, and it must be the last."
                )
            if isinstance(branch, OtherwiseBranch):
                self.otherwise_branch = branch
        if self.otherwise_branch is None:
            self.otherwise_branch = (
                OtherwiseBranch(otherwise) if otherwise is not None else None
            )
            self.pw_branches: tuple[PiecewiseBranch, ...] = branches  # type: ignore
            self.branches = (
                branches if otherwise is None else branches + (self.otherwise_branch,)
            )  # type: ignore
        else:
            assert otherwise is None, "Must not specify two otherwise options"
            self.pw_branches: tuple[PiecewiseBranch, ...] = branches[:-1]  # type: ignore

        conditions = [branch.condition for branch in self.pw_branches]
        negs = [neg(cond) for cond in conditions]
        conjunction = And(*negs) if len(negs) > 1 else negs[0]
        exor_conds = ExOr(*conditions) if len(conditions) > 1 else conditions[0]
        exor = ExOr(*conditions, conjunction)
        disj = Or(exor_conds, conjunction)
        exor.is_assumption = True
        disj.is_assumption = True
        self.knowledge_base.update({exor, disj})
        if self.branches is None:
            self.branches: tuple[*Ps] = branches
        self._init_args = branches
        self._init_kwargs = {"otherwise": otherwise, "name": name}

    def evaluate(self, knowledge_base: set[Proposition] | None = None) -> Term:
        """
        For now, we assume the knowledge base contains only proven propositions.
        """
        from pylogic.helpers import find_first
        from pylogic.proposition.and_ import And
        from pylogic.proposition.or_ import Or

        knowledge_base = knowledge_base or set()

        for branch in self.branches:
            # TODO: check if branch is_proven or true by definition / by_simplification
            if (
                isinstance(branch, OtherwiseBranch)
                or branch.condition in knowledge_base
            ):
                return branch.then

        # We check again if the branch is a disjunction or a conjunction type
        for branch in self.branches:
            if isinstance(branch.condition, And):
                if all(c in knowledge_base for c in branch.condition.propositions):
                    return branch.then
            elif isinstance(branch.condition, Or):
                first_in_kbs = find_first(
                    lambda c: c in knowledge_base,
                    branch.condition.propositions,
                )
                if first_in_kbs[1]:
                    return branch.then
        return self

    def to_sympy(self) -> sp.Basic:
        # TODO: add from_sympy Piecewise
        return sp.Piecewise(
            *[
                (branch.then.to_sympy(), branch.condition.to_sympy())
                for branch in self.branches
            ]
        )

    def _latex(self) -> str:
        start = r"\begin{cases}"
        end = r"\end{cases}"
        branches = "\n".join(
            f"{branch.then._latex()} & {branch.condition._latex()} \\"
            for branch in self.branches
        )
        return f"{start}{branches}{end}"

    def __str__(self) -> str:
        return f"Piecewise({', '.join(str(branch) for branch in self.branches)})"


class PiecewiseBranch(Expr, Generic[P]):
    """
    Represents one branch of a piecewise function.
    Technicially, this should not be used in isolation,
    but only as part of a PiecewiseExpr.
    """

    def __init__(self, condition: P, then: Term) -> None:
        super().__init__(condition, then)
        self.condition: P = condition
        self.then: Term = then
        self._init_args = (condition, then)
        self._init_kwargs = {}

    def evaluate(self) -> Term:
        return self

    def to_sympy(self) -> sp.Basic:
        # TODO: add from sympy PiecewiseBranch
        return sp.functions.elementary.piecewise.ExprCondPair(
            self.then.to_sympy(), self.condition.to_sympy()
        )

    def _latex(self) -> str:
        return (
            rf"\text{{if}} {self.condition._latex()} \text{{then}} {self.then._latex()}"
        )

    def __str__(self) -> str:
        return f"({self.condition}, {self.then})"


class OtherwiseBranch(Expr):
    def __init__(self, then: Term) -> None:
        self.then: Term = then
        super().__init__(then)
        self._init_args = (then,)
        self._init_kwargs = {}

    def evaluate(self) -> Term:
        return self

    def to_sympy(self) -> sp.Basic:
        sp.functions.elementary.piecewise.ExprCondPair(self.then.to_sympy(), True)

    def _latex(self) -> str:
        return rf"\text{{otherwise}} {self.then._latex()}"

    def __str__(self) -> str:
        return f"otherwise({self.then})"


def otherwise(then: Term) -> OtherwiseBranch:
    return OtherwiseBranch(then)
