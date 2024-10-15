from __future__ import annotations

from typing import TYPE_CHECKING, Callable, Generic
from typing import Sequence as TSequence
from typing import TypeVar, cast

from pylogic import Term
from pylogic.proposition.ordering.greaterorequal import GreaterOrEqual

if TYPE_CHECKING:
    pass

    from pylogic.constant import Constant
    from pylogic.expressions.sequence_term import SequenceTerm
    from pylogic.proposition.relation.contains import IsContainedIn
    from pylogic.structures.set_ import Set
    from pylogic.variable import Variable

    T = TypeVar("T", bound=Term)
    C = TypeVar("C", bound="Set")
else:
    T = TypeVar("T")
    C = TypeVar("C")


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

    def __eq__(self, other: object) -> bool:
        if isinstance(other, Sequence):
            return self.name == other.name and self.initial_terms == other.initial_terms
        return NotImplemented

    def __hash__(self) -> int:
        return hash(
            self.name,
            self.nth_term,
            self.is_infinite,
            *self.initial_terms,
        )

    def __getitem__(self, index: int) -> SequenceTerm[T]:
        from pylogic.expressions.sequence_term import SequenceTerm

        return SequenceTerm(self, index)

    def is_in(self, set_: Set | Variable) -> IsContainedIn:
        """
        Return the proposition self in `set`.
        """
        return set_.contains(self)


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
        from pylogic.inference import Inference
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
            self.size,
            len(self.initial_terms),
            _is_proven=True,
            _assumptions=set(),
            _inference=Inference(None, rule="by_definition"),
        )


class Pair(FiniteSequence[T]):
    """
    A pair is a finite sequence with two terms.
    """

    def __init__(self, name: str, first: T, second: T) -> None:
        super().__init__(name, [first, second], size=2)
        self.first = first
        self.second = second

    def __repr__(self) -> str:
        return f"Pair({self.first}, {self.second})"

    def __str__(self) -> str:
        return f"({self.first}, {self.second})"


class Triple(FiniteSequence[T]):
    """
    A triple is a finite sequence with three terms.
    """

    def __init__(self, name: str, first: T, second: T, third: T) -> None:
        super().__init__(name, [first, second, third], size=3)
        self.first = first
        self.second = second
        self.third = third

    def __repr__(self) -> str:
        return f"Triple({self.first}, {self.second}, {self.third})"

    def __str__(self) -> str:
        return f"({self.first}, {self.second}, {self.third})"
