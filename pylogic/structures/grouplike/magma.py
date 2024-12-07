from __future__ import annotations

from typing import Callable, Iterable, TypedDict, TypeVar, Unpack

from pylogic.expressions.expr import BinaryExpression, Expr
from pylogic.infix.infix import SpecialInfix
from pylogic.proposition.quantified.forall import ForallInSet
from pylogic.proposition.relation.contains import IsContainedIn
from pylogic.structures.set_ import Set
from pylogic.typing import Term
from pylogic.variable import Variable

T = TypeVar("T", bound=Term)
E = TypeVar("E", bound=Expr)

AttrNames = TypedDict(
    "AttrNames",
    {
        "operation_name": str,
        "operation_symbol": str,
        "operation": str,
        "op": str,
        "is_closed_under_op": str,
    },
)


class CustomAttrNamesKwargs(TypedDict):
    name: str
    elements: Iterable | None
    containment_function: Callable[..., bool] | None
    operation: Callable[[Term, Term], Expr] | None
    operation_name: str | None
    operation_symbol: str | None
    attr_names: AttrNames


class Magma(Set):
    is_closed_under_op: ForallInSet[ForallInSet[IsContainedIn]]

    # TODO: if operation.symbol is None, this will look weird
    @classmethod
    def property_is_closed_under_op(
        cls,
        set_: Set,
        operation: SpecialInfix[Term, Term, Expr, Expr],
    ) -> ForallInSet[ForallInSet[IsContainedIn]]:
        x = Variable("x")
        y = Variable("y")
        x_op_y = x | operation | y
        return ForallInSet(
            x,
            set_,
            ForallInSet(y, set_, IsContainedIn(x_op_y, set_)),
            description=f"{set_.name} is closed under the operation {operation.symbol}",
        )

    @classmethod
    def _initialize_with_custom_attr_names(
        cls, set_instance, **kwargs: Unpack[CustomAttrNamesKwargs]
    ) -> None:
        cls.__init__(set_instance, **kwargs)

    def __init__(
        self,
        name: str,
        elements: Iterable[T] | None = None,
        containment_function: Callable[[T], bool] | None = None,
        operation: Callable[[T, T], E] | None = None,
        operation_name: str | None = None,
        operation_symbol: str | None = None,
        **kwargs,
    ):
        from pylogic.inference import Inference

        # we use this because we want to be able to change the attribute names
        # when we initialize instances in other classes
        attr_names = kwargs.pop(
            "attr_names",
            {
                "operation_name": "operation_name",
                "operation_symbol": "operation_symbol",
                "operation": "operation",
                "op": "op",
                "is_closed_under_op": "is_closed_under_op",
            },
        )
        self.attr_names = attr_names

        # TODO: need to check that the set is closed under the operation
        # make this functionality optional
        Set.__init__(self, name, elements, containment_function, **kwargs)  # type: ignore
        self._init_args = (name,)
        self._init_kwargs = {
            "elements": elements,
            "containment_function": containment_function,
            "operation": operation,
            "operation_name": operation_name,
            "operation_symbol": operation_symbol,
        }
        self._init_kwargs.update(kwargs)
        opname = operation_name or f"{self.name}_Op"
        opsymb = operation_symbol or f"{self.name}_Op"
        setattr(self, attr_names["operation_name"], opname)
        setattr(
            self, attr_names["operation_symbol"], operation_symbol or f"{self.name}_Op"
        )

        def bin_op_func(x: T, y: T) -> E:
            if operation is None:
                return BinaryExpression(
                    opname, opsymb, x, y, None  # type: ignore
                )  # type: ignore
            result = operation(x, y)
            result.knowledge_base.add(
                IsContainedIn(
                    result,
                    self,
                    _is_proven=True,
                    _inference=Inference(None, rule="by_definition"),
                )
            )
            self.elements.add(result)
            return result

        op = SpecialInfix(
            operate=bin_op_func,
            call=bin_op_func,
            symbol=operation_symbol or f"{self.name}_Op",
        )
        setattr(self, attr_names["operation"], op)
        setattr(self, attr_names["op"], op)
        setattr(
            self,
            attr_names["is_closed_under_op"],
            Magma.property_is_closed_under_op(self, op),
        )
        getattr(self, attr_names["is_closed_under_op"])._set_is_axiom(True)

    def containment_function(self, x: Term) -> bool:
        from pylogic.helpers import python_to_pylogic

        x = python_to_pylogic(x)
        if isinstance(x, BinaryExpression):
            return (
                x.name == getattr(self, self.attr_names["operation_name"])
                and x.symbol == getattr(self, self.attr_names["operation_symbol"])
                and all(self.containment_function(arg) for arg in x.args)
            )
        return super().containment_function(x)
