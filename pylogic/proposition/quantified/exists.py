from __future__ import annotations
from pylogic.proposition.proposition import Proposition
from pylogic.proposition.quantified.quantified import _Quantified
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from sympy import Basic as SympyExpression
from pylogic.set.sets import Set
import sympy as sp
import pylogic.p_symbol as ps


class Exists(_Quantified):
    def __init__(
        self,
        existential_var_name: str,
        expression_to_replace: Set | SympyExpression,
        inner_proposition: Proposition,
        positions: list[list[int]] | None = None,
        existential_var_type: type[Set] | type[sp.Basic] = ps.Symbol,
        is_assumption: bool = False,
        show_arg_position_names: bool = False,
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
        if existential_var_type in [ps.Symbol, ps.Function, ps.MatrixSymbol]:
            is_real = (
                isinstance(expression_to_replace, int)
                or isinstance(expression_to_replace, float)
                or expression_to_replace.is_real
            )
            existential_var = existential_var_type(existential_var_name, real=is_real)  # type: ignore
            existential_var._is_arbitrary = False  # type: ignore
        else:
            # Set
            existential_var = Set(sp.Set(existential_var_name))
            existential_var._is_arbitrary = False
        inner_proposition = inner_proposition.replace(
            expression_to_replace, existential_var, positions=positions
        )
        quantified_arg = ("arg0", existential_var)
        super().__init__(
            "exists",
            inner_proposition,
            is_assumption,
            quantified_arg,
            show_arg_position_names,
            _is_proven,
        )
        self.existential_var = existential_var

    def __iter__(self):
        return iter((self.existential_var, self.inner_proposition))

    def copy(self):
        return super().copy(self)
