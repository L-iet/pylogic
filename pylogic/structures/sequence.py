from __future__ import annotations

from typing import TYPE_CHECKING, Callable, Generic, Self
from typing import Sequence as TSequence
from typing import TypeVar, cast

from pylogic import Term
from pylogic.proposition.ordering.greaterorequal import GreaterOrEqual

if TYPE_CHECKING:
    from pylogic.constant import Constant
    from pylogic.expressions.sequence_term import SequenceTerm
    from pylogic.proposition.proposition import Proposition
    from pylogic.proposition.relation.contains import IsContainedIn
    from pylogic.proposition.relation.equals import Equals
    from pylogic.structures.set_ import SeqSet, Set
    from pylogic.variable import Variable

    T = TypeVar("T", bound=Term)
    C = TypeVar("C", bound="Set")
else:
    T = TypeVar("T")
    C = TypeVar("C")


class Sequence(Generic[T]):
    """
    A sequence is a countably infinite or finite ordered list of elements.

    Parameters:
        predicate: `Callable[[Term], Proposition] | None`
        A function that receives a natural number and returns a proposition.
        sequence.predicate() actually receives a natural number n and returns a proposition
        about the corresponding sequence term.
        So `forall n, predicate(n)` is True.

        Note that if a term `x` is the nth term of the sequence, then `predicate(n)`
        is True, but if some predicate is True for `x`, it doesn't necessarily mean that
        `x` is in the sequence.
    """

    def __init__(
        self,
        name: str,
        initial_terms: TSequence[T] | None = None,
        nth_term: Callable[[int], T] | None = None,
        predicate: Callable[[Term], Proposition] | None = None,
    ) -> None:
        from pylogic.constant import Constant
        from pylogic.expressions.abs import Abs

        init_inds = (
            list(map(Constant, range(len(initial_terms)))) if initial_terms else []
        )

        self.name: str = name
        self.initial_terms: list[T] = list(initial_terms) if initial_terms else []
        self.terms: dict[Constant[int], T] = dict(zip(init_inds, self.initial_terms))
        self.nth_term: Callable[[Term], T] | None = nth_term
        self.is_finite: bool | None = None
        self._predicate: Callable[[Term], Proposition] | None = predicate
        self._predicate_uses_self = predicate is not None
        self.size = Abs(self)

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
            (
                self.name,
                self.nth_term,
                self.is_finite,
                *self.initial_terms,
            )
        )

    def __getitem__(self, index: Term) -> SequenceTerm[T]:
        from pylogic.expressions.sequence_term import SequenceTerm

        return SequenceTerm(self, index)

    def equals(self, other: Term, **kwargs) -> Equals:
        from pylogic.proposition.relation.equals import Equals

        return Equals(self, other, **kwargs)

    def is_in(self, set_: Set | Variable) -> IsContainedIn:
        """
        Return the proposition `self in set_`.
        """
        return set_.contains(self)

    def contains(
        self, other: Term, is_assumption: bool = False, **kwargs
    ) -> IsContainedIn[Term, SeqSet]:
        """elementhood"""
        from pylogic.proposition.relation.contains import IsContainedIn
        from pylogic.structures.set_ import SeqSet

        return IsContainedIn(other, SeqSet(self), is_assumption=is_assumption, **kwargs)

    def evaluate(self) -> Self:
        return self

    def to_sympy(self):
        raise NotImplementedError

    def _latex(self, printer=None) -> str:
        return self.name

    def define_predicate(
        self,
        predicate: Callable[[Term], Proposition],
        predicate_uses_self: bool = False,
    ) -> None:
        """
        Define the predicate that the sequence satisfies.
        Parameters:
            predicate: `Callable[[Term], Proposition]`

                A function that receives a natural number and returns a proposition.
                sequence.predicate() actually receives a natural number n and returns a proposition
                about the corresponding sequence term.
                So for all n, predicate(n) should be True.

            predicate_uses_self: bool

                Whether the predicate uses `self`  (imported from pylogic.sequence) as opposed to the
                reference of the actual sequence.
                If `define_predicate` is being called, the sequence is already initialized and can
                be referenced directly in the predicate. In this case, `predicate_uses_self` should be False.
                If `self` is used in the predicate, `predicate_uses_self` should be True.
                This facilitates replacing `self` with the actual sequence instance when the predicate is called.
        """
        self._predicate = predicate
        if predicate_uses_self:
            self._predicate_uses_self = True

    def predicate(inst, expr: Term) -> Proposition:
        """
        Return the proposition that the term satisfies the predicate.

        expr: Term
            an expression that corresponds to a natural number.
        """
        from pylogic.helpers import python_to_pylogic
        from pylogic.inference import Inference

        expr = python_to_pylogic(expr)
        assert expr.is_natural, "The argument must be a natural number"
        if inst._predicate is None:
            raise ValueError("No predicate was provided")
        res = inst._predicate(expr)

        # if the predicate was defined at initialization, replace the dummy self sequence
        # with this instance
        if self._predicate_uses_self:
            res = res.replace({self: inst})
        res._set_is_proven(True)
        res.from_assumptions = set()
        res.deduced_from = Inference(None, rule="by_predicate")
        return res


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


self = Sequence("_PylogicSelfSeq")
