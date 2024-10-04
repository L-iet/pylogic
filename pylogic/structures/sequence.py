from typing import TYPE_CHECKING, Callable, Generic, Iterable
from typing import Sequence as TSequence
from typing import TypeVar, cast

from pylogic import Term
from pylogic.proposition.ordering.greaterorequal import GreaterOrEqual

if TYPE_CHECKING:
    from fractions import Fraction

    from pylogic.constant import Constant
    from pylogic.expressions.expr import Expr
    from pylogic.expressions.sequence_term import SequenceTerm
    from pylogic.structures.set_ import Set
    from pylogic.symbol import Symbol

    T = TypeVar("T", bound=Term)
    C = TypeVar("C", bound="Set")


class Sequence(Generic[T]):
    """
    A sequence is a countably infinite or finite ordered list of elements.
    """

    def __init__(
        self,
        name: str,
        initial_terms: TSequence[T] | None = None,
        nth_term: Callable[[int], T] | None = None,
    ) -> None:
        self.name: str = name
        self.initial_terms: list[T] = list(initial_terms) if initial_terms else []
        self.terms: dict[int, T] = dict(enumerate(self.initial_terms))
        self.nth_term: Callable[[int], T] | None = nth_term
        self.is_infinite: bool | None = None
        # TODO self.size: Term | None = None

    def __repr__(self) -> str:
        return f"Sequence({self.name})"

    def __str__(self) -> str:
        return self.name

    def __getitem__(self, index: int) -> SequenceTerm[T]:
        from pylogic.expressions.sequence_term import SequenceTerm

        return SequenceTerm(self, index)


class PeriodicSequence(Sequence[T]):
    """
    A periodic sequence is an infinite sequence that repeats after a
    certain number of terms.
    """

    def __init__(
        self,
        name: str,
        initial_terms: TSequence[T] | None = None,
        period: int | Constant[int] | None = None,
        **kwargs,
    ) -> None:
        super().__init__(name, initial_terms, **kwargs)
        self.is_infinite = True
        self.period = period  # TODO: or infinite when None

    def __getitem__(self, index: int) -> SequenceTerm[T]:
        if self.period is not None:
            index %= int(self.period)
        return super().__getitem__(index)


class FiniteSequence(Sequence[T]):
    """
    A finite sequence is a sequence with a finite number of terms.
    """

    def __init__(
        self,
        name: str,
        initial_terms: TSequence[T] | None = None,
        size: Term | None = None,
        **kwargs,
    ) -> None:
        from pylogic.constant import Constant
        from pylogic.expressions.abs import Abs
        from pylogic.helpers import type_check
        from pylogic.variable import Variable

        type_check(
            size, Variable, Constant, int, type(None), context="FiniteSequence.__init__"
        )
        size = cast(Variable | Constant | int | None, size)
        if isinstance(size, int):
            size = Constant(size)
        if (
            isinstance(size, Constant)
            and isinstance(size.value, int)
            and size.value < (len(initial_terms) if initial_terms else 0)
        ):
            raise ValueError(
                "The size of the sequence must be at least the number of initial terms"
            )
        super().__init__(name, initial_terms, **kwargs)
        self.is_infinite = False
        self.size = Abs(self) if size is None else size
        # TODO self.size_is_finite = self.size.is_in(Naturals0, _is_proven=True)
        self.size_at_least = GreaterOrEqual(
            self.size, len(self.initial_terms), _is_proven=True
        )
