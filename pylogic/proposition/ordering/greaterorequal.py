from __future__ import annotations

from typing import TYPE_CHECKING, TypeVar

from pylogic.inference import Inference
from pylogic.proposition.ordering.greaterthan import GreaterThan
from pylogic.proposition.ordering.ordering import _Ordering
from pylogic.proposition.ordering.total import TotalOrder
from pylogic.proposition.proposition import get_assumptions
from pylogic.proposition.relation.equals import Equals
from pylogic.typing import Term

if TYPE_CHECKING:
    from pylogic.proposition.or_ import Or

T = TypeVar("T", bound=Term)
U = TypeVar("U", bound=Term)


class GreaterOrEqual(TotalOrder[T, U], _Ordering):
    name = "GreaterOrEqual"
    infix_symbol = ">="
    infix_symbol_latex = r"\geq"

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
            name="GreaterOrEqual",
            is_assumption=is_assumption,
            description=description,
            **kwargs,
        )

    def by_inspection_check(self) -> bool | None:
        inspec = super().by_inspection_check()
        if inspec is not None:
            return inspec
        if self.right == 0:
            return self.left.is_nonnegative

    def to_disjunction(self) -> Or[GreaterThan, Equals]:
        """If self is of the form `a >= b`, returns a proposition of the form `a > b or a = b`"""
        return GreaterThan(self.left, self.right).or_(
            Equals(self.left, self.right),
            is_assumption=self.is_assumption,
            description=self.description,
            _is_proven=self._is_proven,
            _assumptions=get_assumptions(self),
            _inference=Inference(self, rule="to_disjunction"),
        )

    def add_nonnegative_to_left(self, nonnegative: Term) -> GreaterOrEqual:
        """Logical inference rule.
        If self is of the form `a >= b` and `c` is nonnegative, returns a
        proposition of the form `a + c >= b`"""
        from pylogic.helpers import python_to_pylogic

        nonnegative = python_to_pylogic(nonnegative)
        assert nonnegative.is_nonnegative, f"{nonnegative} is not nonnegative"
        return GreaterOrEqual(
            self.left + nonnegative,
            self.right,
            _is_proven=self.is_proven,
            _assumptions=get_assumptions(self),
            _inference=Inference(self, rule="add_nonnegative_to_left"),
        )

    def add_positive_to_left(self, positive: Term) -> GreaterThan:
        """Logical inference rule.
        If self is of the form `a >= b` and `c` is positive, returns a
        proposition of the form `a + c > b`"""
        from pylogic.helpers import python_to_pylogic

        positive = python_to_pylogic(positive)
        assert positive.is_positive, f"{positive} is not positive"
        return GreaterThan(
            self.left + positive,
            self.right,
            _is_proven=self.is_proven,
            _assumptions=get_assumptions(self),
            _inference=Inference(self, rule="add_positive_to_left"),
        )

    def add_nonpositive_to_right(self, nonpositive: Term) -> GreaterOrEqual:
        """Logical inference rule.
        If self is of the form `a >= b` and `c` is nonpositive (c <= 0), returns a
        proposition of the form `a >= b + c`"""
        from pylogic.helpers import python_to_pylogic

        nonpositive = python_to_pylogic(nonpositive)
        assert nonpositive.is_nonpositive, f"{nonpositive} is not nonpositive"
        return GreaterOrEqual(
            self.left,
            self.right + nonpositive,
            _is_proven=self.is_proven,
            _assumptions=get_assumptions(self),
            _inference=Inference(self, rule="add_nonpositive_to_right"),
        )

    def add_negative_to_right(self, negative: Term) -> GreaterThan:
        """Logical inference rule.
        If self is of the form `a >= b` and `c` is negative, returns a
        proposition of the form `a > b + c`"""
        from pylogic.helpers import python_to_pylogic

        negative = python_to_pylogic(negative)
        assert negative.is_negative, f"{negative} is not negative"
        return GreaterThan(
            self.left,
            self.right + negative,
            _is_proven=self.is_proven,
            _assumptions=get_assumptions(self),
            _inference=Inference(self, rule="add_negative_to_right"),
        )
