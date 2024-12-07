from typing import TYPE_CHECKING, Any

if TYPE_CHECKING:
    from decimal import Decimal
    from fractions import Fraction

    from pylogic.expressions.expr import Expr
    from pylogic.structures.sequence import Sequence
    from pylogic.structures.set_ import Set
    from pylogic.symbol import Symbol
    from pylogic.variable import Variable

    PythonNumeric = Fraction | int | float | complex | Decimal
    PBasic = Symbol | Sequence | Set
    Unevaluated = Symbol | Sequence | Set | Expr
    Term = Unevaluated
    Unification = dict[Variable, Term]
else:
    Term = Any
    PythonNumeric = Any
    PBasic = Any
    Unevaluated = Any
    Unification = Any
