from __future__ import annotations

from fractions import Fraction
from typing import TYPE_CHECKING, Any, Callable, Iterable, Self, TypeAlias, TypeVar

from pylogic.constant import Constant
from pylogic.expressions.expr import Add, Mul
from pylogic.expressions.function import Function
from pylogic.proposition.and_ import And
from pylogic.proposition.implies import Implies
from pylogic.proposition.not_ import Not
from pylogic.proposition.ordering.greaterorequal import GreaterOrEqual
from pylogic.proposition.ordering.greaterthan import GreaterThan
from pylogic.proposition.ordering.lessorequal import LessOrEqual
from pylogic.proposition.ordering.lessthan import LessThan
from pylogic.proposition.proposition import Proposition
from pylogic.proposition.quantified.exists import ExistsInSet
from pylogic.proposition.quantified.forall import ForallInSet, ForallSubsets
from pylogic.proposition.relation.equals import Equals
from pylogic.structures.ordered_set import OrderedSet
from pylogic.structures.ringlike.semiring import SemirIng
from pylogic.structures.set_ import Set
from pylogic.typing import Term, Unevaluated
from pylogic.variable import Variable

if TYPE_CHECKING:
    from pylogic.expressions.expr import BinaryExpression, Expr
    from pylogic.proposition.ordering.total import StrictTotalOrder, TotalOrder
    from pylogic.proposition.relation.contains import IsContainedIn
    from pylogic.proposition.relation.divides import Divides

    T = TypeVar("T", bound=Term)
    E = TypeVar("E", bound=Expr)
    Z = TypeVar("Z", str, int, float, complex, Fraction)

    BinOpFunc: TypeAlias = Callable[[T, T], BinaryExpression[T]]
    TotalOrderOp: TypeAlias = Callable[..., TotalOrder]
    StrictTotalOrderOp: TypeAlias = Callable[..., StrictTotalOrder]
else:
    T = Any
    E = Any
    Z = Any
    BinOpFunc = Any
    TotalOrderOp = Any
    StrictTotalOrderOp = Any
zero = Constant(0)
one = Constant(1)


class NaturalsSemiring(SemirIng, OrderedSet):
    successor: Function
    closed_under_successor: ForallInSet[IsContainedIn]
    successor_injective = ForallInSet[ForallInSet[Implies[Equals, Equals]]]
    successor_neq_0: ForallInSet[Not[Equals]]
    zero_is_min_nat: ForallInSet[TotalOrder]

    # forall subsets of N, if 0 is in the subset
    # and for all n in N,
    #    (for each k <= n, k is in the subset) implies (n+1 is in the subset)
    # then the subset is N
    strong_induction_formal: ForallSubsets[
        Implies[
            And[
                IsContainedIn,
                ForallInSet[
                    Implies[
                        ForallInSet[Implies[TotalOrder, IsContainedIn]], IsContainedIn
                    ]
                ],
            ],
            Equals,
        ]
    ]
    well_ordering_set: ForallSubsets[
        Implies[Not[Equals], ExistsInSet[ForallInSet[TotalOrder]]]
    ]

    @classmethod
    def property_closed_under_successor(
        cls,
        set_: Set,
        successor: Function,
        **kwargs,
    ) -> ForallInSet[IsContainedIn]:
        from pylogic.proposition.relation.contains import IsContainedIn

        x = Variable("x")
        return ForallInSet(
            x,
            set_,
            IsContainedIn(successor(x), set_),
            description=f"{set_.name} is closed under the successor function {successor.name}",
        )

    @classmethod
    def property_successor_injective(
        cls,
        set_: Set,
        successor: Function,
        **kwargs,
    ) -> ForallInSet[ForallInSet[Implies[Equals, Equals]]]:
        x = Variable("x")
        y = Variable("y")
        return ForallInSet(
            x,
            set_,
            ForallInSet(
                y,
                set_,
                Implies(
                    Equals(successor(x), successor(y)),
                    Equals(x, y),
                ),
            ),
            description=f"{successor.name} is injective (one-to-one) on {set_.name}",
        )

    @classmethod
    def property_successor_neq_0(
        cls,
        set_: Set,
        successor: Function,
        zero: Constant,
        **kwargs,
    ) -> ForallInSet[Not[Equals]]:
        x = Variable("x")
        return ForallInSet(
            x,
            set_,
            Not(Equals(successor(x), zero)),
            description=f"The successor of any element is not 0",
        )

    @classmethod
    def property_strong_induction_formal(
        cls,
        set_: Set,
        total_order: TotalOrderOp,
        successor: Function,
        zero: Constant,
        **kwargs,
    ) -> ForallSubsets[
        Implies[
            And[
                IsContainedIn,
                ForallInSet[
                    Implies[
                        ForallInSet[Implies[TotalOrder, IsContainedIn]], IsContainedIn
                    ]
                ],
            ],
            Equals,
        ]
    ]:
        """
        This uses second order logic (quantifying over subsets of N) to state the principle of strong induction.
        This is formal in the sense that it uses the successor function without evaluating it.
        """
        s = Variable("s", set_=True)
        n = Variable("n")
        k = Variable("k")
        return ForallSubsets(
            s,
            set_,
            And(
                zero.is_in(s),
                ForallInSet(
                    n,
                    set_,
                    ForallInSet(k, set_, total_order(k, n).implies(k.is_in(s))).implies(
                        successor(n).is_in(s)
                    ),
                ),
            ).implies(s.equals(set_)),
            description=f"Formal Strong induction for set {set_}",
        )

    @classmethod
    def property_well_ordering_set(
        cls, set_: Set, total_order: TotalOrderOp, **kwargs
    ) -> ForallSubsets[Implies[Not[Equals], ExistsInSet[ForallInSet[TotalOrder]]]]:
        from pylogic.structures.set_ import EmptySet

        s = Variable("s", set_=True)
        x = Variable("x")
        n = Variable("n")
        return ForallSubsets(
            s,
            set_,
            Not(s.equals(EmptySet)).implies(
                ExistsInSet(n, s, ForallInSet(x, s, total_order(n, x)))  # type: ignore
            ),
            description=f"Every non-empty subset of {set_.name} has a least element",
        )

    @classmethod
    def property_zero_is_min_nat(
        cls, set_: Set, total_order: TotalOrderOp, zero: Constant, **kwargs
    ) -> ForallInSet[TotalOrder]:
        n = Variable("n")
        return ForallInSet(
            n,
            set_,
            total_order(zero, n),
            description=f"{zero} is the minimum element of {set_.name}",
        )

    def __init__(
        self,
        name: str,
        elements: Iterable[T] | None = None,
        containment_function: Callable[[T], bool] | None = None,
        plus_operation: Callable[[T, T], E] | None = None,
        plus_operation_symbol: str | None = None,
        zero: Z | Unevaluated | None = None,
        times_operation: Callable[[T, T], E] | None = None,
        times_operation_symbol: str | None = None,
        one: Z | Unevaluated | None = None,
        total_order: TotalOrderOp | None = None,
        strict_total_order: StrictTotalOrderOp | None = None,
        **kwargs,
    ):
        SemirIng.__init__(
            self,
            name=name,
            elements=elements,
            containment_function=containment_function,
            plus_operation=plus_operation,
            plus_operation_symbol=plus_operation_symbol,
            zero=zero,
            times_operation=times_operation,
            times_operation_symbol=times_operation_symbol,
            one=one,
            **kwargs,
        )
        OrderedSet.__init__(
            self,
            name=name,
            elements=elements,
            containment_function=containment_function,
            total_order=total_order,
            strict_total_order=strict_total_order,
            **kwargs,
        )
        self._init_args = (name,)
        self._init_kwargs = {
            "elements": elements,
            "containment_function": containment_function,
            "plus_operation": plus_operation,
            "plus_operation_symbol": plus_operation_symbol,
            "zero": zero,
            "times_operation": times_operation,
            "times_operation_symbol": times_operation_symbol,
            "one": one,
            "total_order": total_order,
            "strict_total_order": strict_total_order,
        }
        self._init_kwargs.update(kwargs)

        x = Variable("x")
        self.successor = Function(
            "Naturals.successor", self, self, parameters=(x,), definition=x + 1
        )
        self.closed_under_successor = NaturalsSemiring.property_closed_under_successor(
            self, self.successor
        )
        self.closed_under_successor._set_is_axiom(True)

        self.well_ordering_set = NaturalsSemiring.property_well_ordering_set(
            self, self.total_order
        )
        self.well_ordering_set._set_is_axiom(True)
        self.less_or_equal = LessOrEqual
        self.less_than = LessThan
        self.greater_than = GreaterThan
        self.greater_or_equal = GreaterOrEqual

        # TODO: this should be a theorem
        self.zero_is_min_nat = NaturalsSemiring.property_zero_is_min_nat(
            self, self.total_order, zero
        )
        self.zero_is_min_nat.todo(_internal=True)

    def strong_induction(
        self,
        base_case: Proposition,
        induction_step: ForallInSet[
            Implies[ForallInSet[Implies[TotalOrder, Proposition]], Proposition]
        ],
    ) -> ForallInSet[Proposition]:
        r"""
        Logical inference rule. This uses the principle of strong induction given the base case and inductive step.
        Given base case P(0) and induction step
        forall n in N:
            forall k in N: (k <= n -> P(k))
            implies P(n+1),
        return a proof of forall n: n in N -> P(n).
        """
        assert base_case.is_proven, f"Base case {base_case} must be proven"
        assert (
            induction_step.is_proven
        ), f"Induction step {induction_step} must be proven"
        from pylogic.inference import Inference

        match induction_step:
            case ForallInSet(
                variable=n1,
                set_=induc_set,
                _inner_without_set=Implies(
                    antecedent=ForallInSet(
                        variable=k1,
                        _inner_without_set=Implies(
                            antecedent=TotalOrder(left=k2, right=n2),
                            consequent=p_k,
                        ),
                    ),
                    consequent=p__n_plus_1,
                ),
            ):
                if (
                    induc_set == self
                    and n1 == n2
                    and k1 == k2
                    and p_k.replace({k1: 0}).eval_same(base_case)
                    and p_k.replace({k1: n1 + one}).eval_same(p__n_plus_1)
                ):
                    return ForallInSet(
                        n1,
                        self,
                        p_k.replace({k1: n1}),
                        _is_proven=True,
                        _assumptions=base_case.from_assumptions.union(
                            induction_step.from_assumptions
                        ),
                        _inference=Inference(
                            base_case, induction_step, rule="strong_induction"
                        ),
                    )
        print("Base Case:")
        print(base_case.as_text())
        print("Induction Step:")
        print(induction_step.as_text())
        raise ValueError(
            "Base case or induction step do not match the expected form\
You may have dangling assumptions whose scopes are not properly closed."
        )

    def weak_induction(
        self,
        base_case: Proposition,
        induction_step: ForallInSet[Implies[Proposition, Proposition]],
    ) -> ForallInSet[Proposition]:
        r"""
        Logical inference rule. This uses the principle of weak induction given the base case and inductive step.
        Given base case P(0) and induction step
        forall n in N: P(n) -> P(n+1),
        return a proof of forall n in N, P(n).
        """
        assert base_case.is_proven, f"Base case {base_case} must be proven"
        assert (
            induction_step.is_proven
        ), f"Induction step {induction_step} must be proven"
        from pylogic.inference import Inference

        match induction_step:
            case ForallInSet(
                variable=n1,
                set_=induc_set,
                _inner_without_set=Implies(antecedent=p_n, consequent=p__n_plus_1),
            ):
                if (
                    induc_set == self
                    and p_n.replace({n1: zero}).eval_same(base_case)
                    and p_n.replace({n1: n1 + 1}).eval_same(p__n_plus_1)
                ):
                    return ForallInSet(
                        n1,
                        self,
                        p_n,
                        _is_proven=True,
                        _assumptions=base_case.from_assumptions.union(
                            induction_step.from_assumptions
                        ),
                        _inference=Inference(
                            base_case, induction_step, rule="weak_induction"
                        ),
                    )
        print("Base Case:")
        print(base_case.as_text())
        print("Induction Step:")
        print(induction_step.as_text())
        raise ValueError(
            "Base case and induction step do not match the expected form \
You may have dangling assumptions whose scopes are not properly closed."
        )

    def even(self, n: Term, **kwargs) -> ExistsInSet[Equals]:
        from pylogic.helpers import python_to_pylogic

        n = python_to_pylogic(n)
        k = Variable("k")
        return ExistsInSet(
            k,
            self,
            Equals(n, 2 * k),
            description=f"{n} is even",
            **kwargs,
        )

    def odd(self, n: Term, **kwargs) -> ExistsInSet[Equals]:
        from pylogic.helpers import python_to_pylogic

        n = python_to_pylogic(n)
        k = Variable("k")
        return ExistsInSet(
            k,
            self,
            Equals(n, 2 * k + 1),
            description=f"{n} is odd",
            **kwargs,
        )

    def divides(self, a: Term, b: Term, **kwargs) -> Divides:
        from pylogic.proposition.relation.divides import Divides

        return Divides(a, b, self, **kwargs)

    def prime(self, n: Term, **kwargs) -> Prime:
        return Prime(n, **kwargs)

    def well_ordering(
        self, prop: Proposition, argument: Term | None = None
    ) -> ExistsInSet[And[Proposition, ForallInSet[Implies[Proposition, TotalOrder]]]]:
        r"""
        Logical inference rule. Given a proposition about naturals, prove that there is a
        least natural number satisfying it.
        If argument is provided, it should be an argument of the proposition
        and will be used in patter-matching to construct the result.
        """
        from pylogic.inference import Inference
        from pylogic.proposition.proposition import get_assumptions
        from pylogic.proposition.quantified.exists import ExistsInSet
        from pylogic.proposition.relation.contains import IsContainedIn

        assert prop.is_proven, f"{prop} must be proven"
        x = Variable("x")
        n = Variable("n")
        match prop:
            case ExistsInSet(variable=x1, _inner_without_set=Px1):
                return ExistsInSet(
                    n,
                    self,
                    Px1.replace({x1: n}).and_(
                        ForallInSet(
                            x,
                            self,
                            Implies(Px1.replace({x1: x}), self.total_order(n, x)),
                        )
                    ),
                    _is_proven=True,
                    _assumptions=get_assumptions(prop),
                    _inference=Inference(prop, rule="well_ordering"),
                )
            case And(propositions=(IsContainedIn(left=x0, right=s), Px0)) if s == self:
                return ExistsInSet(
                    n,
                    self,
                    Px0.replace({x0: n}).and_(
                        ForallInSet(
                            x,
                            self,
                            Implies(Px0.replace({x0: x}), self.total_order(n, x)),
                        )
                    ),
                    _is_proven=True,
                    _assumptions=get_assumptions(prop),
                    _inference=Inference(prop, rule="well_ordering"),
                )
            case Proposition() if argument is not None:
                return ExistsInSet(
                    n,
                    self,
                    prop.replace({argument: n}).and_(
                        ForallInSet(
                            x,
                            self,
                            Implies(
                                prop.replace({argument: x}), self.total_order(n, x)
                            ),
                        )
                    ),
                    _is_proven=True,
                    _assumptions=get_assumptions(prop),
                    _inference=Inference(prop, rule="well_ordering"),
                )
        raise ValueError("Proposition does not match expected form")


Naturals = NaturalsSemiring(
    "Naturals",
    containment_function=lambda x: getattr(x, "is_natural", False),
    plus_operation=Add,
    plus_operation_symbol="+",
    times_operation=Mul,
    times_operation_symbol="*",
    zero=zero,
    one=one,
    total_order=LessOrEqual,
    strict_total_order=LessThan,
    latex_name="\\mathbb{N}",
)
Naturals._is_real = True
Naturals._is_rational = True
Naturals._is_integer = True
Naturals._is_natural = True
Naturals._is_nonnegative = True


class Prime(Proposition):
    """
    Represents a number being prime.
    """

    _repr_uses_is = True
    _repr_after_is = "prime"

    def __init__(self, n: Term, description: str = "", **kwargs) -> None:
        super().__init__("Prime", args=[n], **kwargs)

        n = self.args[0]
        a = Variable("a")
        b = Variable("b")
        # works for prime element of a ring
        self._definition = Not(n.equals(0)).and_(
            Not(n.equals(1)),  # technically, n has no multiplicative inverse
            ForallInSet(
                a,
                Naturals,
                ForallInSet(
                    b,
                    Naturals,
                    Naturals.divides(n, a * b).implies(
                        Naturals.divides(n, a).or_(Naturals.divides(n, b))
                    ),
                ),
            ),
            description=description or f"{n} is prime",
            **kwargs,
        )
        self.n = n

        if (
            kwargs.get("_is_proven")
            or kwargs.get("is_assumption")
            or kwargs.get("is_axiom")
        ):
            self._set_is_inferred(True)

        self._set_init_inferred_attrs()

    @property
    def definition(self) -> And:
        return self._definition

    def __str__(self) -> str:
        from pylogic.enviroment_settings.settings import settings

        if settings["SHOW_ALL_PARENTHESES"]:
            n_str = f"({self.n})" if not self.n.is_atomic else str(self.n)
        else:
            n_str = str(self.n)
        return f"{n_str} is prime"

    def __repr__(self) -> str:
        return f"Prime({self.n})"

    def _latex(self) -> str:
        from pylogic.enviroment_settings.settings import settings

        if settings["SHOW_ALL_PARENTHESES"]:
            n_latex = (
                f"({self.n._latex()})" if not self.n.is_atomic else self.n._latex()
            )
        else:
            n_latex = self.n._latex()
        return f"{n_latex} \\text{{ is prime }}"

    def _set_is_inferred(self, value: bool) -> None:
        super()._set_is_inferred(value)
        if value:
            self.n.knowledge_base.add(self)
        else:
            self.n.knowledge_base.discard(self)
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
            inner_positions = [p[1:] for p in positions if p[0] == 0]
            return self.__class__(
                self.n.replace(replace_dict, inner_positions, equal_check),
                is_assumption=self.is_assumption,
                is_axiom=self.is_axiom,
                description=self.description,
            )
        return self.__class__(
            self.n.replace(replace_dict, equal_check=equal_check),
            is_assumption=self.is_assumption,
            is_axiom=self.is_axiom,
            description=self.description,
        )

    def by_inspection_check(self) -> bool | None:
        from pylogic.helpers import is_prime, is_python_real_numeric

        if isinstance(self.n, Constant) and is_python_real_numeric(self.n.value):
            return is_prime(self.n.value)
        return None

    def copy(self) -> Self:
        return self.__class__(
            self.n,
            is_assumption=self.is_assumption,
            is_axiom=self.is_axiom,
            description=self.description,
            _is_proven=self._is_proven,
            _inference=self.deduced_from,
            _assumptions=self.from_assumptions,
        )

    def deepcopy(self) -> Self:
        return self.__class__(
            self.n.deepcopy(),
            is_assumption=self.is_assumption,
            is_axiom=self.is_axiom,
            description=self.description,
            _is_proven=self._is_proven,
            _inference=self.deduced_from,
            _assumptions=self.from_assumptions,
        )
