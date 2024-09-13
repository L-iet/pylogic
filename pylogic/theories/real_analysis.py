from pylogic.constant import Constant
from pylogic.expressions.expr import Add, Mul
from pylogic.structures.ringlike.ordered_field import OrderedField

zero = Constant(0)
one = Constant(1)


class RealsField(OrderedField):
    pass


Reals = RealsField(
    "Reals",
    plus_operation=Add,
    plus_operation_symbol="+",
    times_operation=Mul,
    times_operation_symbol="*",
    zero=zero,
    one=one,
)
