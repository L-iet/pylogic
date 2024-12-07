from __future__ import annotations

from typing import Any, Callable, Iterable, TypeAlias, TypeVar

from pylogic.expressions.expr import BinaryExpression, Expr
from pylogic.infix.infix import SpecialInfix
from pylogic.proposition.quantified.forall import ForallInSet
from pylogic.proposition.relation.contains import IsContainedIn
from pylogic.structures.grouplike.magma import Magma
from pylogic.structures.set_ import Set
from pylogic.typing import Term

T = TypeVar("T", bound=Term)
E = TypeVar("E", bound=Expr)
BinOpFunc: TypeAlias = Callable[[T, T], BinaryExpression[T]]


class _RingoidCommon(Set):
    """
    A ringoid is a set closed under two binary operations + and *,
    where * distributes over +.
    """

    is_closed_under_plus: ForallInSet[ForallInSet[IsContainedIn]]
    is_closed_under_times: ForallInSet[ForallInSet[IsContainedIn]]

    @classmethod
    def property_is_closed_under_plus(
        cls,
        set_: Set,
        plus_operation: SpecialInfix[Term, Term, Expr, Expr],
    ) -> ForallInSet[ForallInSet[IsContainedIn]]:
        return Magma.property_is_closed_under_op(set_, plus_operation)

    @classmethod
    def property_is_closed_under_times(
        cls,
        set_: Set,
        times_operation: SpecialInfix[Term, Term, Expr, Expr],
    ) -> ForallInSet[ForallInSet[IsContainedIn]]:
        return Magma.property_is_closed_under_op(set_, times_operation)

    def __init__(
        self,
        name: str,
        elements: Iterable[T] | None = None,
        containment_function: Callable[[T], bool] | None = None,
        plus_operation: Callable[[T, T], E] | None = None,
        plus_operation_symbol: str | None = None,
        times_operation: Callable[[T, T], E] | None = None,
        times_operation_symbol: str | None = None,
        **kwargs,
    ):
        Set.__init__(self, name, elements, containment_function, **kwargs)  # type: ignore
        self._init_args = (name,)
        self._init_kwargs = {
            "elements": elements,
            "containment_function": containment_function,
            "plus_operation": plus_operation,
            "plus_operation_symbol": plus_operation_symbol,
            "times_operation": times_operation,
            "times_operation_symbol": times_operation_symbol,
        }
        self._init_kwargs.update(kwargs)
        self.plus_operation_name = f"{self.name}_+"
        self.plus_operation_symbol = plus_operation_symbol or f"{self.name}_+"
        self.plus_eval_func = plus_operation
        self.times_operation_name = f"{self.name}_*"
        self.times_operation_symbol = times_operation_symbol or f"{self.name}_*"
        self.times_eval_func = times_operation

        self.plus_operation: SpecialInfix[T, T, E, E]
        self.times_operation: SpecialInfix[T, T, E, E]
        # we inject the appropriate values using the Magma constructor into custom attribute names
        Magma._initialize_with_custom_attr_names(
            self,
            name=name,
            elements=elements,
            containment_function=containment_function,
            operation=plus_operation,  # type: ignore
            operation_name=f"{self.name}_+",
            operation_symbol=plus_operation_symbol or f"{self.name}_+",
            attr_names={
                "operation_name": f"plus_operation_name",
                "operation_symbol": "plus_operation_symbol",
                "operation": "plus_operation",
                "op": "plus_op",
                "is_closed_under_op": "is_closed_under_plus",
            },
        )
        Magma._initialize_with_custom_attr_names(
            self,
            name=name,
            elements=elements,
            containment_function=containment_function,
            operation=times_operation,  # type: ignore
            operation_name=f"{self.name}_*",
            operation_symbol=times_operation_symbol or f"{self.name}_*",
            attr_names={
                "operation_name": f"times_operation_name",
                "operation_symbol": "times_operation_symbol",
                "operation": "times_operation",
                "op": "times_op",
                "is_closed_under_op": "is_closed_under_times",
            },
        )

        self.plus = self.plus_operation
        self.times = self.times_operation

    def _replace_instance_set(self, _instance_set: Set, _property: str) -> Any:
        orig_prop = getattr(_instance_set, _property)
        ret_val = orig_prop.replace(
            {_instance_set: self}, equal_check=lambda x, y: x is y
        )
        ret_val._set_is_axiom(orig_prop.is_axiom)
        ret_val._set_is_proven(orig_prop._is_proven)
        ret_val._set_is_assumption(orig_prop.is_assumption)
        ret_val.from_assumptions = orig_prop.from_assumptions
        ret_val.deduced_from = orig_prop.deduced_from
        return ret_val

    def containment_function(self, x: Term) -> bool:
        if isinstance(x, BinaryExpression):
            return (
                (
                    x.symbol == self.plus_operation_symbol
                    and x.eval_func is self.plus_eval_func
                )
                or (
                    x.symbol == self.times_operation_symbol
                    and x.eval_func is self.times_eval_func
                )
            ) and all(self.containment_function(arg) for arg in x.args)
        return super().containment_function(x)
