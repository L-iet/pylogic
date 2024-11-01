from __future__ import annotations

from fractions import Fraction
from typing import TYPE_CHECKING, Any, Callable, Iterable, TypeAlias, TypeVar

from pylogic import Term, Unevaluated
from pylogic.constant import Constant
from pylogic.expressions.expr import Add, Mul
from pylogic.expressions.function import Function
from pylogic.proposition.and_ import And
from pylogic.proposition.implies import Implies
from pylogic.proposition.not_ import Not
from pylogic.proposition.ordering.lessorequal import LessOrEqual
from pylogic.proposition.ordering.lessthan import LessThan
from pylogic.proposition.quantified.exists import ExistsInSet
from pylogic.proposition.quantified.forall import ForallInSet, ForallSubsets
from pylogic.proposition.relation.equals import Equals
from pylogic.structures.ordered_set import OrderedSet
from pylogic.structures.ringlike.semiring import SemirIng
from pylogic.structures.set_ import Set
from pylogic.variable import Variable

if TYPE_CHECKING:
    from pylogic.expressions.expr import BinaryExpression, Expr
    from pylogic.proposition.ordering.total import StrictTotalOrder, TotalOrder
    from pylogic.proposition.proposition import Proposition
    from pylogic.proposition.relation.contains import IsContainedIn

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
        )
        OrderedSet.__init__(
            self,
            name=name,
            elements=elements,
            containment_function=containment_function,
            total_order=total_order,
            strict_total_order=strict_total_order,
        )
        self.successor = Function("Naturals.successor", self, self)
        self.well_ordering_set = NaturalsSemiring.property_well_ordering_set(
            self, self.total_order
        )
        self.well_ordering_set._set_is_axiom(True)
        self.less_or_equal = LessOrEqual
        self.less_than = LessThan

        # TODO: this should be a theorem
        self.zero_is_min_nat = NaturalsSemiring.property_zero_is_min_nat(
            self, self.total_order, zero
        )
        self.zero_is_min_nat._set_is_axiom(True)

    def strong_induction(
        self,
        base_case: Proposition,
        induction_step: ForallInSet[
            Implies[ForallInSet[Implies[TotalOrder, Proposition]], Proposition]
        ],
    ) -> ForallInSet[Proposition]:
        r"""
        Logical tactic. This uses the principle of strong induction given the base case and inductive step.
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
                    n1 == n2
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
        Logical tactic. This uses the principle of weak induction given the base case and inductive step.
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
                _inner_without_set=Implies(antecedent=p_n, consequent=p__n_plus_1),
            ):
                if p_n.replace({n1: zero}).eval_same(base_case) and p_n.replace(
                    {n1: n1 + 1}
                ).eval_same(p__n_plus_1):
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

    def divides(self, a: Term, b: Term, **kwargs) -> ExistsInSet[Equals]:
        from pylogic.helpers import python_to_pylogic

        a = python_to_pylogic(a)
        b = python_to_pylogic(b)
        k = Variable("k")
        return ExistsInSet(
            k,
            self,
            Equals(a * k, b),
            description=f"{a} divides {b}",
            **kwargs,
        )

    def prime(self, n: Term, **kwargs) -> ...:
        # TODO: implement
        from pylogic.helpers import python_to_pylogic

    def well_ordering(
        self, prop: Proposition, argument: Term | None = None
    ) -> ExistsInSet[And[Proposition, ForallInSet[Implies[Proposition, TotalOrder]]]]:
        r"""
        Logical tactic. Given a proposition about naturals, prove that there is a
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
)
