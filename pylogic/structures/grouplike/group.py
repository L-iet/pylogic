from __future__ import annotations

from fractions import Fraction
from typing import TYPE_CHECKING, Callable, Iterable, TypeVar, cast

from sympy import Basic
from sympy import Set as SympySet

from pylogic.expressions.expr import BinaryExpression, Expr
from pylogic.infix.infix import SpecialInfix
from pylogic.proposition.and_ import And
from pylogic.proposition.implies import Implies
from pylogic.proposition.quantified.exists import ExistsUniqueInSet
from pylogic.proposition.quantified.forall import Forall, ForallInSet
from pylogic.proposition.relation.contains import IsContainedIn
from pylogic.proposition.relation.equals import Equals
from pylogic.structures.grouplike.monoid import Monoid
from pylogic.structures.set_ import Set
from pylogic.symbol import Symbol
from pylogic.variable import Variable

Numeric = Fraction | int | float
PBasic = Symbol | Numeric
Unevaluated = Symbol | Set | Expr
Term = Unevaluated | Numeric | Basic

T = TypeVar("T", bound=Term)
E = TypeVar("E", bound=Expr)


class Group(Monoid):
    latin_square: ForallInSet[
        ForallInSet[And[ExistsUniqueInSet[Equals], ExistsUniqueInSet[Equals]]]
    ]
    have_inverses: ForallInSet[ExistsUniqueInSet[And[Equals, Equals]]]

    @classmethod
    def property_latin_square(
        cls,
        set_: Set,
        operation: SpecialInfix[Term, Term, Expr, Expr],
    ) -> ForallInSet[
        ForallInSet[And[ExistsUniqueInSet[Equals], ExistsUniqueInSet[Equals]]]
    ]:
        r"""
        The Latin square property states that, for each a and b in Q,
        there exist unique elements x and y in Q such that both

        a * x = b

        y * a = b

        Then x = a \ b (left divide) and y = b / a (right divide)
        """
        from pylogic.structures.grouplike.quasigroup import Quasigroup

        return Quasigroup.property_latin_square(set_, operation)

    @classmethod
    def property_have_inverses(
        cls,
        set_: Set,
        operation: SpecialInfix[Term, Term, Expr, Expr],
        identity: Term,
    ) -> ForallInSet[ExistsUniqueInSet[And[Equals, Equals]]]:
        """
        This is a theorem because it is a consequence of the Latin square property
        and the identity property.
        """
        a = Variable("a")
        x = Variable("x")
        return ForallInSet(
            a,
            set_,
            ExistsUniqueInSet(
                x,
                set_,
                Equals(a | operation | x, identity).and_(
                    Equals(x | operation | a, identity)
                ),
            ),
            description=f"Every element in {set_.name} has an inverse",
        )

    def __init__(
        self,
        name: str | None = None,
        sympy_set: SympySet | None = None,
        elements: Iterable[T] | None = None,
        containment_function: Callable[[T], bool] | None = None,
        operation: Callable[[T, T], E] | None = None,
        operation_name: str | None = None,
        operation_symbol: str | None = None,
        identity: T | None = None,
    ):
        super().__init__(
            name,
            sympy_set,
            elements,
            containment_function,
            operation,
            operation_name,
            operation_symbol,
            identity,
        )
        a = Variable("a")
        self.latin_square = Group.property_latin_square(self, self.operation)
        self.latin_square.is_axiom = True

        # From the Latin square property, we can deduce that every element in
        # the group has a left inverse and a right inverse
        a_in_self = a.is_in(self, is_assumption=True)
        left_and_right_inverses = self.latin_square.in_particular(
            a, a_in_self
        ).in_particular(self.identity)
        l_inv, r_inv = left_and_right_inverses
        cx, Pxs = l_inv.extract()
        cx_in_self, right_inv_eq, cx_unique = cast(
            tuple[IsContainedIn, Equals, Forall[Implies[Equals, Equals]]],
            Pxs.extract(),
        )
        cy, Pys = r_inv.extract()
        cy_in_self, left_inv_eq, cy_unique = cast(
            tuple[IsContainedIn, Equals, Forall[Implies[Equals, Equals]]],
            Pys.extract(),
        )
        identity_property = self.has_identity.extract()[1]

        def transitive_proof(
            left_inv: Term,
            right_inv: Term,
            left_inv_eq: Equals,
            right_inv_eq: Equals,
            left_inv_in_self: IsContainedIn,
            right_inv_in_self: IsContainedIn,
        ) -> Equals:
            # This is a template of a proof that makes some equations
            # and uses transitivity to prove the desired equation that the
            # left inverse is equal to the right inverse.
            # cx is the right inverse of a, cy is the left inverse of a
            cx_eq_e_op_cx = identity_property.in_particular(
                right_inv, proof_expr_to_substitute_in_set=right_inv_in_self
            )[1].symmetric()
            e_op_cx_eq_cy_op_a__op_cx = left_inv_eq.symmetric().apply(
                lambda t: t | self.op | right_inv
            )
            assoc = (
                self.op_is_associative.in_particular(left_inv, left_inv_in_self)
                .in_particular(a, a_in_self)
                .in_particular(right_inv, right_inv_in_self)
            )
            cy_op__a_op_cx_eq_cy_op_e = right_inv_eq.apply(
                lambda t: left_inv | self.op | t
            )
            cy_op_e_eq_cy = identity_property.in_particular(
                left_inv, proof_expr_to_substitute_in_set=left_inv_in_self
            )[0]
            cx_eq_cy = cx_eq_e_op_cx.transitive(
                e_op_cx_eq_cy_op_a__op_cx,
                assoc,
                cy_op__a_op_cx_eq_cy_op_e,
                cy_op_e_eq_cy,
            )
            return cx_eq_cy

        # use the left and right inverses to prove that they are equal
        cx_eq_cy = transitive_proof(
            cy, cx, left_inv_eq, right_inv_eq, cy_in_self, cx_in_self
        )
        # replace cy with cx in the left inverse equation
        cx_op_a_eq_e = cx_eq_cy.p_substitute_into("left", left_inv_eq)
        cx_inv_property = cx_in_self.p_and(right_inv_eq, cx_op_a_eq_e)

        # Now we prove that the inverse is unique
        w = Variable("w")
        w_in_self = w.is_in(self, is_assumption=True)
        w_is_right_inv = (a | self.op | w).equals(self.identity, is_assumption=True)
        w_is_left_inv = (w | self.op | a).equals(self.identity, is_assumption=True)

        # similar algebraic proof as above
        w_eq_cx = transitive_proof(
            cx, w, cx_op_a_eq_e, w_is_right_inv, cx_in_self, w_in_self
        )
        cx_unique_property = w_eq_cx.followed_from(
            w_in_self, w_is_right_inv, w_is_left_inv
        ).thus_forall(w)

        self.have_inverses = (
            cx_inv_property.p_and(cx_unique_property)
            .thus_there_exists("a_inv", cx)
            .to_exists_unique_in_set()
            .thus_forall_in_set(a, self)
        )  # type: ignore


class AbelianGroup(Group):
    op_is_commutative: ForallInSet[ForallInSet[Equals]]

    @classmethod
    def property_op_is_commutative(
        cls,
        set_: Set,
        operation: SpecialInfix[Term, Term, Expr, Expr],
    ) -> ForallInSet[ForallInSet[Equals]]:
        x = Variable("x")
        y = Variable("y")
        x_op_y = x | operation | y
        return ForallInSet(
            x,
            set_,
            ForallInSet(
                y,
                set_,
                Equals(x_op_y, y | operation | x),
            ),
            description=f"{operation.symbol} is commutative in {set_.name}",
        )

    def __init__(
        self,
        name: str | None = None,
        sympy_set: SympySet | None = None,
        elements: Iterable[T] | None = None,
        containment_function: Callable[[T], bool] | None = None,
        operation: Callable[[T, T], E] | None = None,
        operation_name: str | None = None,
        operation_symbol: str | None = None,
        identity: T | None = None,
    ):
        super().__init__(
            name,
            sympy_set,
            elements,
            containment_function,
            operation,
            operation_symbol,
            operation_name,
            identity,
        )
        self.op_is_commutative = AbelianGroup.property_op_is_commutative(
            self, self.operation
        )
        self.op_is_commutative.is_axiom = True
