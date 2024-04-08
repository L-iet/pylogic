from __future__ import annotations
from pylogic.proposition.proposition import Proposition
from pylogic.proposition.quantified.quantified import _Quantified
from pylogic.variable import Variable
from typing import TYPE_CHECKING, Generic, TypeVar, Self

if TYPE_CHECKING:
    from sympy import Basic

    SympyExpression = Basic | int | float
from pylogic.set.sets import Set
import sympy as sp
import pylogic.p_symbol as ps


class Exists(_Quantified):
    def __init__(
        self,
        existential_var_name: str,
        expression_to_replace: Set | SympyExpression | None,
        inner_proposition: Proposition,
        positions: list[list[int]] | None = None,
        is_assumption: bool = False,
        is_real: bool = True,
        _is_proven: bool = False,
    ) -> None:
        r"""
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
        """
        variable = Variable(existential_var_name, real=is_real)
        if expression_to_replace is not None:
            inner_proposition = inner_proposition.replace(
                expression_to_replace, variable, positions=positions
            )
        super().__init__(
            "exists",
            variable,
            inner_proposition,
            is_assumption,
            _is_proven,
        )

    def __iter__(self):
        return iter((self.variable, self.inner_proposition))

    def copy(self) -> Self:
        return self.__class__(
            self.variable.name,
            None,
            self.inner_proposition.copy(),
            [],
            self.is_assumption,
            self.variable.is_real or False,
            self.is_proven,
        )
