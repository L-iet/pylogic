from __future__ import annotations

from typing import TYPE_CHECKING, Callable, Generic, Self
from typing import Sequence as TSequence
from typing import TypeVar, cast

from pylogic import PythonNumeric, Term
from pylogic.proposition.ordering.greaterorequal import GreaterOrEqual

if TYPE_CHECKING:
    from sympy.series.sequences import SeqBase, SeqFormula, SeqPer

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

    is_atomic = True

    def __init__(
        self,
        name: str,
        initial_terms: TSequence[T] | None = None,
        nth_term: Callable[[int], T] | None = None,
        predicate: Callable[[Term], Proposition] | None = None,
        real: bool | None = None,
        **kwargs,
    ) -> None:
        from pylogic.assumptions_context import assumptions_contexts
        from pylogic.constant import Constant
        from pylogic.expressions.abs import Abs
        from pylogic.helpers import _add_assumption_attributes, _add_assumptions
        from pylogic.inference import Inference
        from pylogic.proposition.quantified.forall import ForallInSet
        from pylogic.variable import Variable

        init_inds = (
            list(map(Constant, range(len(initial_terms)))) if initial_terms else []
        )

        self.name: str = name
        self.knowledge_base: set[Proposition] = set()
        self.initial_terms: list[T] = list(initial_terms) if initial_terms else []
        self.terms: dict[Constant[int], T] = dict(zip(init_inds, self.initial_terms))
        self.nth_term: Callable[[Term], T] | None = nth_term
        self.is_finite: bool | None = None
        self._predicate: Callable[[Term], Proposition] | None = predicate
        self._predicate_uses_self = predicate is not None

        self._is_real: bool | None = real
        self._is_rational: bool | None = kwargs.get("rational", None)
        self._is_integer: bool | None = kwargs.get("integer", None)
        self._is_natural: bool | None = kwargs.get("natural", None)

        self.is_set_: bool | None = kwargs.get("set_", None)
        self.is_set: bool | None = self.is_set_
        self.is_graph: bool | None = not self.is_set and kwargs.get("graph", None)
        self.is_pair: bool | None = self.is_graph or kwargs.get("pair", None)
        self.is_list_: bool | None = self.is_pair or kwargs.get("list_", None)
        self.is_list: bool | None = self.is_list_
        self.is_sequence: bool | None = self.is_list or kwargs.get("sequence", None)

        self._is_zero: bool | None = kwargs.get("zero", None)
        self._is_nonpositive: bool | None = kwargs.get("nonpositive", None)
        self._is_nonnegative: bool | None = kwargs.get("nonnegative", None)
        self._is_even: bool | None = kwargs.get("even", None)

        _add_assumption_attributes(self, kwargs)

        self.properties_of_each_term: list[Proposition] = []

        # TODO: See Symbol.__init__
        for attr in [
            "real",
            "rational",
            "integer",
            "natural",
            "zero",
            "nonpositive",
            "nonnegative",
            "even",
        ]:
            if getattr(self, f"_is_{attr}") is not None:
                from pylogic.theories.natural_numbers import Naturals

                n = Variable("n")
                self_n = self[n]
                prop = _add_assumptions(self_n, attr, getattr(self, f"_is_{attr}"))
                prop = ForallInSet(
                    n,
                    Naturals,
                    prop,
                    _is_proven=True,
                    _assumptions=set(),
                    _inference=Inference(None, rule="by_definition"),
                )
                self.knowledge_base.add(prop)
                self.properties_of_each_term.append(prop)
                if assumptions_contexts[-1] is not None:
                    assumptions_contexts[-1].assumptions.append(prop)

        # needs to be here, after setting all above attributes
        self.size = Abs(self)

        self._init_args = (name,)
        self._init_kwargs = {
            "initial_terms": initial_terms,
            "nth_term": nth_term,
            "predicate": predicate,
            "real": real,
            **kwargs,
        }

    @property
    def is_natural(self) -> bool | None:
        return self._is_natural

    @property
    def is_integer(self) -> bool | None:
        return self._is_integer or self.is_natural

    @property
    def is_rational(self) -> bool | None:
        return self._is_rational or self.is_integer

    @property
    def is_real(self) -> bool | None:
        return self._is_real or self.is_rational

    @property
    def is_zero(self) -> bool | None:
        return self._is_zero

    @property
    def is_nonzero(self) -> bool | None:
        from pylogic.helpers import ternary_not

        return ternary_not(self.is_zero)

    @property
    def is_even(self) -> bool | None:
        return self._is_even

    @property
    def is_odd(self) -> bool | None:
        from pylogic.helpers import ternary_not

        return ternary_not(self.is_even)

    @property
    def is_positive(self) -> bool | None:
        from pylogic.helpers import ternary_and

        return ternary_and(self.is_nonnegative, self.is_nonzero)

    @property
    def is_negative(self) -> bool | None:
        from pylogic.helpers import ternary_and

        return ternary_and(self.is_nonpositive, self.is_nonzero)

    @property
    def is_nonpositive(self) -> bool | None:
        return self._is_nonpositive

    @property
    def is_nonnegative(self) -> bool | None:
        return self._is_nonnegative

    def __repr__(self) -> str:
        return f"Sequence({self.name})"

    def __str__(self) -> str:
        return f"({self.name}_n)"

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
        return rf"\left({self.name}_n\right)"

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
        from pylogic.variable import Variable

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

    def to_sympy(self) -> SeqBase | SeqFormula:
        from sympy import oo

        from pylogic.sympy_helpers import PylSympySeqBase, PylSympySeqFormula

        if self.nth_term is not None:
            n = Variable("n")
            return PylSympySeqFormula(
                self.nth_term(n).to_sympy(),
                (n.to_sympy(), 0, oo),
                _pyl_class=self.__class__,
                _pyl_init_args=self._init_args,
                _pyl_init_kwargs=self._init_kwargs,
            )
        return PylSympySeqBase(
            self.name,
            _pyl_class=self.__class__,
            _pyl_init_args=self._init_args,
            _pyl_init_kwargs=self._init_kwargs,
        )


class PeriodicSequence(Sequence[T]):
    """
    A periodic sequence is an infinite sequence that repeats after a
    certain number of terms.
    """

    def __init__(
        self,
        name: str,
        initial_terms: TSequence[T] | None = None,
        period: int | Constant[int] | T | None = None,
        **kwargs,
    ) -> None:
        super().__init__(name, initial_terms, **kwargs)
        from pylogic.helpers import python_to_pylogic

        self.is_finite = False
        self.period = python_to_pylogic(period)  # TODO: or infinite when None

        self._init_args = (name,)
        self._init_kwargs = {
            "initial_terms": initial_terms,
            "period": period,
            **kwargs,
        }

    def __getitem__(self, index: Term) -> SequenceTerm[T]:
        from pylogic.helpers import is_integer_numeric

        if (
            self.period is not None
            and is_integer_numeric(self.period)
            and is_integer_numeric(index)
        ):
            index = int(index)
            index %= int(self.period)
        return super().__getitem__(index)

    def to_sympy(self) -> SeqBase | SeqPer:
        from sympy.series.sequences import SeqPer

        from pylogic.sympy_helpers import PylSympySeqBase

        if self.initial_terms is not None and self.period == len(self.initial_terms):
            return SeqPer(
                [term.to_sympy() for term in self.initial_terms],
            )
        return PylSympySeqBase(
            self.name,
            _pyl_class=self.__class__,
            _pyl_init_args=self._init_args,
            _pyl_init_kwargs=self._init_kwargs,
        )


class FiniteSequence(Sequence[T]):
    """
    A finite sequence is a sequence with a finite number of terms.
    """

    def __init__(
        self,
        name: str,
        initial_terms: TSequence[T] | None = None,
        length: Term | PythonNumeric | None = None,
        **kwargs,
    ) -> None:
        from pylogic.constant import Constant
        from pylogic.expressions.abs import Abs
        from pylogic.helpers import type_check
        from pylogic.inference import Inference
        from pylogic.variable import Variable

        type_check(
            length,
            Variable,
            Constant,
            int,
            type(None),
            context="FiniteSequence.__init__",
        )
        if (
            isinstance(length, Constant)
            and isinstance(length.value, float)
            and length.value != float("inf")
        ):
            raise ValueError("The length of a sequence must be an integer")
        _length = cast(Term | None, length)
        if isinstance(length, int):
            _length = Constant(length)
        if (
            isinstance(_length, Constant)
            and isinstance(_length.value, int)
            and _length.value < (len(initial_terms) if initial_terms else 0)
        ):
            raise ValueError(
                "The length of the sequence must be at least the number of initial terms"
            )
        super().__init__(name, initial_terms, **kwargs)
        self.is_finite = True
        self.length = _length
        # TODO self.size_is_finite = self.size.is_in(Naturals0, _is_proven=True)
        self.size_at_least = GreaterOrEqual(
            self.size,
            len(self.initial_terms),
            _is_proven=True,
            _assumptions=set(),
            _inference=Inference(None, rule="by_definition"),
        )
        if _length is not None:
            self.size_at_least = self.size_at_least.and_(
                self.size.equals(_length),
                _is_proven=True,
                _assumptions=set(),
                _inference=Inference(None, rule="by_definition"),
            )

        self._init_args = (name,)
        self._init_kwargs = {
            "initial_terms": initial_terms,
            "length": length,
            **kwargs,
        }

    def to_sympy(self) -> SeqBase | SeqPer:
        from sympy.series.sequences import SeqPer

        from pylogic.sympy_helpers import PylSympySeqBase

        if self.initial_terms is not None:
            return SeqPer(
                [term.to_sympy() for term in self.initial_terms],
                (0, len(self.initial_terms) - 1),
            )
        return PylSympySeqBase(
            self.name,
            _pyl_class=self.__class__,
            _pyl_init_args=self._init_args,
            _pyl_init_kwargs=self._init_kwargs,
        )


class Pair(FiniteSequence[T]):
    """
    A pair is a finite sequence with two terms.
    """

    def __init__(self, name: str, first: T, second: T) -> None:
        from pylogic.helpers import ternary_and

        super().__init__(
            name,
            [first, second],
            length=2,
            real=ternary_and(first.is_real, second.is_real),
        )
        self.first = first
        self.second = second

        self._init_args = (name, first, second)
        self._init_kwargs = {}

    def __repr__(self) -> str:
        return f"Pair({self.first}, {self.second})"

    def __str__(self) -> str:
        return f"({self.first}, {self.second})"


class Triple(FiniteSequence[T]):
    """
    A triple is a finite sequence with three terms.
    """

    def __init__(self, name: str, first: T, second: T, third: T) -> None:
        from pylogic.helpers import ternary_and

        super().__init__(
            name,
            [first, second, third],
            length=3,
            real=ternary_and(first.is_real, second.is_real, third.is_real),
        )
        self.first = first
        self.second = second
        self.third = third

        self._init_args = (name, first, second, third)
        self._init_kwargs = {}

    def __repr__(self) -> str:
        return f"Triple({self.first}, {self.second}, {self.third})"

    def __str__(self) -> str:
        return f"({self.first}, {self.second}, {self.third})"


self = Sequence("_PylogicSelfSeq")
