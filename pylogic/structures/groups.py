from typing import Callable, TYPE_CHECKING
from pylogic.structures.sets import Set
from pylogic.infix.infix import SpecialInfix

if TYPE_CHECKING:
    from fractions import Fraction
    from pylogic.symbol import Symbol
    from pylogic.expressions.expr import Expr

    from sympy import Basic
    from sympy import Set as SympySet

    Numeric = Fraction | int | float
    PBasic = Symbol | Numeric
    Unevaluated = Symbol | Set | Expr
    Term = Unevaluated | Numeric | Basic


class Group(Set):
    def __init__(
        self,
        name: str | None = None,
        sympy_set: SympySet | None = None,
        containment_function: Callable[[Term], bool] | None = None,
        operation: Callable[[Term, Term], Term] | None = None,
    ):
        super().__init__(name, sympy_set, containment_function)
        self.operation: SpecialInfix[Term, Term, Term, Operation] = SpecialInfix(
            operation or (lambda x, y: x)
        )
