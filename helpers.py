import sympy as sp
from typing import Any

SympyExpression = sp.Basic | int | float


def replace(
    old: SympyExpression, new: SympyExpression, expr: SympyExpression
) -> SympyExpression | Any:
    if expr == old:
        return new
    elif isinstance(expr, sp.Basic):
        return expr.subs(old, new)
    else:
        return expr
