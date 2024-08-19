from __future__ import annotations
from typing import Callable, Iterable, TypeVar
from fractions import Fraction
from pylogic.structures.set_ import Set
from pylogic.structures.quasigroup import Quasigroup
from pylogic.expressions.expr import Expr
from pylogic.symbol import Symbol
from pylogic.constant import Constant
from pylogic.variable import Variable
from pylogic.proposition.quantified.forall import ForallInSet
from pylogic.proposition.relation.equals import Equals

from sympy import Basic
from sympy import Set as SympySet

Numeric = Fraction | int | float
PBasic = Symbol | Numeric
Unevaluated = Symbol | Set | Expr
Term = Unevaluated | Numeric | Basic

T = TypeVar("T", bound=Term)


class Loop(Quasigroup):

    def __init__(
        self,
        name: str | None = None,
        sympy_set: SympySet | None = None,
        elements: Iterable[T] | None = None,
        containment_function: Callable[[T], bool] | None = None,
        operation: Callable[[T, T], T] | None = None,
        operation_symbol: str | None = None,
        identity: T | None = None,
    ):
        if elements is not None and identity is not None:
            assert identity in elements, "Identity must be in the set of elements"
        super().__init__(
            name, sympy_set, elements, containment_function, operation, operation_symbol
        )
        self.identity = Constant(f"{self.name}_Ident")
        self.identity_is_given = (
            Equals(self.identity, identity, is_axiom=True)
            if identity is not None
            else None
        )
        x = Variable("x")
        self.has_identity = ForallInSet(
            x,
            self,
            Equals(x | self.operation | self.identity, x).and_(
                Equals(self.identity | self.operation | x, x)
            ),
            is_axiom=True,
            description=f"{self.identity} is the identity element in {self.name}",
        )

    def containment_function(self, x: Term) -> bool:
        return x == self.identity or self._containment_function(x)
