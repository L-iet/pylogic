from __future__ import annotations

from typing import TYPE_CHECKING, TypeVar

from pylogic.inference import Inference
from pylogic.proposition.ordering.lessthan import LessThan
from pylogic.proposition.ordering.ordering import _Ordering
from pylogic.proposition.ordering.total import TotalOrder
from pylogic.proposition.proposition import get_assumptions
from pylogic.proposition.relation.equals import Equals
from pylogic.typing import Term

if TYPE_CHECKING:
    from pylogic.proposition.or_ import Or

T = TypeVar("T", bound=Term)
U = TypeVar("U", bound=Term)


class LessOrEqual(TotalOrder[T, U], _Ordering):
    name = "LessOrEqual"
    infix_symbol = "<="
    infix_symbol_latex = r"\leq"

    def __init__(
        self,
        left: T,
        right: U,
        is_assumption: bool = False,
        description: str = "",
        name=None,
        **kwargs,
    ) -> None:
        super().__init__(
            left,
            right,
            name="LessOrEqual",
            is_assumption=is_assumption,
            description=description,
            **kwargs,
        )

    def by_inspection_check(self) -> bool | None:
        inspec = super().by_inspection_check()
        if inspec is not None:
            return inspec
        if self.right == 0:
            return self.left.is_nonpositive
    
    def _set_is_inferred(self, value: bool) -> None:
        if value and self.right == 0 and not self.left.is_nonpositive:
            self.left.is_nonpositive = True
        if value and self.left == 0 and not self.right.is_nonnegative:
            self.right.is_nonnegative = True
        super()._set_is_inferred(value)

    def to_disjunction(self) -> Or[LessThan, Equals]:
        """If self is of the form `a <= b`, returns a proposition of the form `a < b or a = b`"""
        return LessThan(self.left, self.right).or_(
            Equals(self.left, self.right),
            is_assumption=self.is_assumption,
            description=self.description,
            _is_proven=self._is_proven,
            _assumptions=get_assumptions(self),
            _inference=Inference(self, rule="to_disjunction"),
        )

    def add_nonnegative_to_right(self, nonnegative: Term) -> LessOrEqual:
        """Logical inference rule.
        If self is of the form `a <= b` and `c` is nonnegative, returns a
        proposition of the form `a <= b + c`"""
        from pylogic.helpers import python_to_pylogic

        nonnegative = python_to_pylogic(nonnegative)
        assert nonnegative.is_nonnegative, f"{nonnegative} is not nonnegative"
        return LessOrEqual(
            self.left,
            self.right + nonnegative,
            _is_proven=self.is_proven,
            _assumptions=get_assumptions(self),
            _inference=Inference(self, rule="add_nonnegative_to_right"),
        )

    def add_positive_to_right(self, positive: Term) -> LessThan:
        """Logical inference rule.
        If self is of the form `a <= b` and `c` is positive, returns a
        proposition of the form `a < b + c`"""
        from pylogic.helpers import python_to_pylogic

        positive = python_to_pylogic(positive)
        assert positive.is_positive, f"{positive} is not positive"
        return LessThan(
            self.left,
            self.right + positive,
            _is_proven=self.is_proven,
            _assumptions=get_assumptions(self),
            _inference=Inference(self, rule="add_positive_to_right"),
        )

    def add_nonpositive_to_left(self, nonpositive: Term) -> LessOrEqual:
        """Logical inference rule.
        If self is of the form `a <= b` and `c` is nonpositive (c <= 0), returns a
        proposition of the form `a + c <= b`"""
        from pylogic.helpers import python_to_pylogic

        nonpositive = python_to_pylogic(nonpositive)
        assert nonpositive.is_nonpositive, f"{nonpositive} is not nonpositive"
        return LessOrEqual(
            self.left + nonpositive,
            self.right,
            _is_proven=self.is_proven,
            _assumptions=get_assumptions(self),
            _inference=Inference(self, rule="add_nonpositive_to_left"),
        )

    def add_negative_to_left(self, negative: Term) -> LessThan:
        """Logical inference rule.
        If self is of the form `a <= b` and `c` is negative, returns a
        proposition of the form `a + c < b`"""
        from pylogic.helpers import python_to_pylogic

        negative = python_to_pylogic(negative)
        assert negative.is_negative, f"{negative} is not negative"
        return LessThan(
            self.left + negative,
            self.right,
            _is_proven=self.is_proven,
            _assumptions=get_assumptions(self),
            _inference=Inference(self, rule="add_negative_to_left"),
        )
