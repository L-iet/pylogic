from typing import TYPE_CHECKING, Any

from pylogic.constant import Constant
from pylogic.expressions.expr import Add, Mul
from pylogic.proposition.ordering.lessorequal import LessOrEqual
from pylogic.proposition.quantified.exists import ExistsInSet, ExistsUniqueInSet
from pylogic.proposition.quantified.forall import ForallInSet, ForallSubsets
from pylogic.structures.ringlike.ordered_field import OrderedField

zero = Constant(0)
one = Constant(1)

if TYPE_CHECKING:
    from pylogic.proposition.implies import Implies

    IsUpperBound = ForallInSet[LessOrEqual]
    IsLowerBound = ForallInSet[LessOrEqual]
    BoundedAbove = ExistsInSet[IsUpperBound]
    BoundedBelow = ExistsInSet[IsLowerBound]
else:
    IsUpperBound = Any
    IsLowerBound = Any
    BoundedAbove = Any
    BoundedBelow = Any


class RealsField(OrderedField):
    bounded_above_has_lub: ForallSubsets[
        Implies[
            BoundedAbove,
            ExistsUniqueInSet[ForallInSet[Implies[IsUpperBound, LessOrEqual]]],
        ]
    ]


Reals = RealsField(
    "Reals",
    plus_operation=Add,
    plus_operation_symbol="+",
    times_operation=Mul,
    times_operation_symbol="*",
    zero=zero,
    one=one,
)
