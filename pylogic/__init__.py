import sys
from typing import TYPE_CHECKING, Any

if not sys.warnoptions:
    import warnings

    from pylogic.warn import PylogicInternalWarning

    warnings.simplefilter("ignore", PylogicInternalWarning)

if TYPE_CHECKING:
    from fractions import Fraction

    from pylogic.expressions.expr import Expr
    from pylogic.structures.sequence import Sequence
    from pylogic.structures.set_ import Set
    from pylogic.symbol import Symbol
    from pylogic.variable import Variable

    Numeric = Fraction | int | float
    PBasic = Symbol | Numeric
    Unevaluated = Symbol | Sequence | Set | Expr
    Term = Unevaluated | Numeric
    Unification = dict[Variable, Term]
else:
    Term = Any
    Numeric = Any
    PBasic = Any
    Unevaluated = Any
    Unification = Any
