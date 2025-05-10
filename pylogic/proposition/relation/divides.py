from fractions import Fraction
from typing import TYPE_CHECKING, Any, Callable, Iterable, Self, TypeAlias, TypeVar

from pylogic.constant import Constant
from pylogic.expressions.expr import Add, Mul
from pylogic.expressions.function import Function
from pylogic.proposition.ordering.lessorequal import LessOrEqual
from pylogic.proposition.ordering.lessthan import LessThan
from pylogic.proposition.proposition import Proposition
from pylogic.proposition.quantified.exists import ExistsInSet
from pylogic.proposition.relation.relation import Relation
from pylogic.structures.ordered_set import OrderedSet
from pylogic.structures.ringlike.ring import RIng
from pylogic.typing import Term, Unevaluated
from pylogic.variable import Variable


class Divides(Relation):
    is_atomic = True

    def __init__(
        self,
        a: Term,
        b: Term,
        quotient_set: Term,
        is_assumption: bool = False,
        description: str = "",
        **kwargs,
    ) -> None:
        super().__init__(
            "Divides",
            is_assumption=is_assumption,
            description=description,
            args=[a, b, quotient_set],
            **kwargs,
        )

        a, b, quotient_set = self.args
        q = Variable("q")
        self._definition = ExistsInSet(
            q,
            quotient_set,
            b.equals(a * q),
            is_assumption=is_assumption,
            description=description or f"{a} divides {b} in {quotient_set}",
            **kwargs,
        )
        self.a = a
        self.b = b
        self.quotient_set = quotient_set
        self._q_var = q
        self._set_init_inferred_attrs()

    def __str__(self) -> str:
        from pylogic.enviroment_settings.settings import settings

        if settings["SHOW_ALL_PARENTHESES"]:
            wrap = lambda p: f"({p})" if not p.is_atomic else str(p)
        else:
            wrap = lambda p: str(p)
        return f"{wrap(self.b)} / {wrap(self.a)} in {wrap(self.quotient_set)}"

    def __repr__(self) -> str:
        return f"Divides({self.a}, {self.b}, {self.quotient_set})"

    def _latex(self) -> str:
        # TODO: may want to change __str__ as well
        from pylogic.enviroment_settings.settings import settings

        if settings["SHOW_ALL_PARENTHESES"]:
            wrap = lambda p: (
                rf"\left({p._latex()}\right)" if not p.is_atomic else p._latex()
            )
        else:
            wrap = lambda p: p._latex()
        if (
            self.quotient_set.name == "Integers"
            and self.quotient_set.__class__.__name__ == "IntegersRing"
        ):
            return f"\\left. {wrap(self.a)} \\middle| {wrap(self.b)} \\right."
        return f"\\left. {wrap(self.a)} \\middle|_{wrap(self.quotient_set)} {wrap(self.b)} \\right."

    def _set_is_inferred(self, value: bool) -> None:
        super()._set_is_inferred(value)
        if value:
            self.a.knowledge_base.add(self)
        else:
            self.a.knowledge_base.discard(self)
        self._definition._set_is_inferred(value)

    def _set_is_proven(self, value: bool, **kwargs) -> None:
        super()._set_is_proven(value, **kwargs)
        self._definition._set_is_proven(value, **kwargs)
        if value:
            from pylogic.inference import Inference
            from pylogic.proposition.proposition import get_assumptions

            self._definition.from_assumptions = get_assumptions(self)
            self._definition.deduced_from = Inference(
                self, conclusion=self._definition, rule="by_definition"
            )

    def _set_is_assumption(self, value: bool, **kwargs) -> None:
        super()._set_is_assumption(value, **kwargs)
        self._definition._set_is_assumption(value)

    def _set_is_axiom(self, value: bool) -> None:
        super()._set_is_axiom(value)
        self._definition._set_is_axiom(value)

    def replace(
        self,
        replace_dict: dict[Term, Term],
        positions: list[list[int]] | None = None,
        equal_check: Callable[[Term, Term], bool] | None = None,
    ) -> Self:
        if positions is not None:
            left_positions = [p[1:] for p in positions if p[0] == 0]
            right_positions = [p[1:] for p in positions if p[0] == 1]
            return self.__class__(
                self.a.replace(replace_dict, left_positions, equal_check),
                self.b.replace(replace_dict, right_positions, equal_check),
                self.quotient_set.replace(replace_dict, equal_check=equal_check),
                is_assumption=self.is_assumption,
                is_axiom=self.is_axiom,
                description=self.description,
            )
        return self.__class__(
            self.a.replace(replace_dict, equal_check=equal_check),
            self.b.replace(replace_dict, equal_check=equal_check),
            self.quotient_set.replace(replace_dict, equal_check=equal_check),
            is_assumption=self.is_assumption,
            is_axiom=self.is_axiom,
            description=self.description,
        )

    def by_inspection_check(self) -> bool | None:
        from pylogic.helpers import is_python_real_numeric

        if isinstance(self.a, Constant) and isinstance(self.b, Constant):
            if is_python_real_numeric(self.a.value) and is_python_real_numeric(
                self.b.value
            ):
                return self.b.value % self.a.value == 0
        return None

    @property
    def definition(self) -> ExistsInSet:
        return self._definition

    def to_exists_in_set(self, **kwargs) -> ExistsInSet:
        return self.definition

    def copy(self) -> Self:
        return self.__class__(
            self.a,
            self.b,
            self.quotient_set,
            is_assumption=self.is_assumption,
            is_axiom=self.is_axiom,
            description=self.description,
            _is_proven=self._is_proven,
            _inference=self.deduced_from,
            _assumptions=self.from_assumptions,
        )

    def deepcopy(self) -> Self:
        return self.__class__(
            self.a.deepcopy(),
            self.b.deepcopy(),
            self.quotient_set.deepcopy(),
            is_assumption=self.is_assumption,
            is_axiom=self.is_axiom,
            description=self.description,
            _is_proven=self._is_proven,
            _inference=self.deduced_from,
            _assumptions=self.from_assumptions,
        )
