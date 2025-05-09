from __future__ import annotations

from fractions import Fraction
from typing import TYPE_CHECKING

import sympy as sp

from pylogic.expressions.expr import Expr, to_sympy
from pylogic.typing import Term

if TYPE_CHECKING:
    from pylogic.constant import Constant


class Mod(Expr):
    """
    The smallest natural number that remains when an integer is divided by another integer.
    """

    _precedence = 6

    def __init__(self, *args, **kwargs) -> None:
        super().__init__(*args, **kwargs)
        self.mutable_attrs_to_copy = self.mutable_attrs_to_copy + [
            "expr",
            "modulus",
            "expr_lt_modulus",
            "expr_gt_modulus",
        ]

    def __new_init__(self, expr: Term, modulus: Term) -> None:
        super().__new_init__(expr, modulus)
        self.expr = self.args[0]
        self.modulus = self.args[1]

    def update_properties(self) -> None:
        from pylogic.helpers import ternary_and, ternary_not
        from pylogic.proposition.ordering.greaterthan import GreaterThan
        from pylogic.proposition.ordering.lessthan import LessThan

        expr, modulus = self.args

        expr_lt_modulus = None
        expr_is_lt_modulus = LessThan(expr, modulus)
        modulus_is_gt_expr = GreaterThan(modulus, expr)
        expr_lt_modulus = (
            (expr_is_lt_modulus in expr.knowledge_base)
            or (modulus_is_gt_expr in modulus.knowledge_base)
            or None
        )

        expr_gt_modulus = None
        expr_is_gt_modulus = GreaterThan(expr, modulus)
        modulus_is_lt_expr = LessThan(modulus, expr)
        expr_gt_modulus = (
            (expr_is_gt_modulus in expr.knowledge_base)
            or (modulus_is_lt_expr in modulus.knowledge_base)
            or None
        )

        self.is_natural = ternary_and(
            expr.is_integer, modulus.is_integer, ternary_not(modulus.is_zero)
        )
        self.is_real = self._is_natural
        self.is_rational = self._is_natural
        self.is_integer = self._is_natural
        self.is_zero = None

        if expr_lt_modulus and self._is_natural:
            self.is_even = expr.is_even
            self.is_odd = expr.is_odd
        elif expr_gt_modulus and self._is_natural:
            if modulus.is_even:
                self.is_even = expr.is_even
                self.is_odd = expr.is_odd
            elif modulus.is_odd:
                # self.is_even and self.is_odd are
                # already None
                pass

        self.is_nonnegative = True if self._is_natural else None
        self.is_nonpositive = self._is_zero

        self.expr_lt_modulus: bool | None = expr_lt_modulus
        self.expr_gt_modulus: bool | None = expr_gt_modulus

    def evaluate(self, **kwargs) -> Term:
        # TODO: fix this to evaluate correctly something like
        # Mod(x+y+z, x+y) -> Mod(z, x+y)
        # Mod(x*y*z, x*y) -> 0
        from pylogic.constant import Constant
        from pylogic.expressions.expr import Add, Mul, Pow
        from pylogic.expressions.prod import Prod
        from pylogic.expressions.sequence_term import SequenceTerm
        from pylogic.expressions.sum import Sum, _Aggregate
        from pylogic.helpers import is_integer_numeric
        from pylogic.sympy_helpers import sympy_to_pylogic
        from pylogic.variable import Variable

        # TODO: feature: add is_polynomial for easy check add, mul, pow
        # base cases
        if self.expr == self.modulus:
            return Constant(0)
        if not self.is_natural:
            return self
        if is_integer_numeric(self.expr) and is_integer_numeric(self.modulus):
            return Constant(self.expr.value % self.modulus.value)

        possible_ret_vals = []
        if isinstance(self.expr, Mod) and self.expr.modulus == self.modulus:
            possible_ret_vals.append(Mod(self.expr.expr, self.modulus).evaluate())

        if not isinstance(self.expr, _Aggregate):
            try:
                possible_ret_vals.append(sympy_to_pylogic(self.to_sympy().doit()))
            except Exception as e:  # see Add.evaluate
                pass

        # (x+y+z) mod (x+y) -> z mod (x+y)
        new_expr1 = (self.expr - self.modulus).evaluate()
        new_expr2 = (self.expr + self.modulus).evaluate()
        new_expr = new_expr1 if len(str(new_expr1)) < len(str(new_expr2)) else new_expr2
        if len(str(new_expr)) < len(str(self.expr)):
            possible_ret_vals.append(Mod(new_expr, self.modulus).evaluate())

        expr_eval = self.expr.evaluate()
        mod_eval = self.modulus.evaluate()
        if expr_eval != self.expr:
            possible_ret_vals.append(Mod(expr_eval, self.modulus).evaluate())
        if mod_eval != self.modulus:
            possible_ret_vals.append(Mod(self.expr, mod_eval).evaluate())

            if expr_eval != self.expr:
                possible_ret_vals.append(Mod(expr_eval, mod_eval).evaluate())

        if isinstance(self.expr, Pow):
            # self.expr.exp must be a natural number
            # since self.expr.is_integer is True
            if self.expr.base == self.modulus:
                return Constant(0)
            new_base = Mod(self.expr.base, self.modulus).evaluate()
            if isinstance(new_base, Mod) and new_base.modulus == self.modulus:
                new_base = new_base.expr
            if new_base == Constant(0):
                return Constant(0)
            new_expr = Pow(new_base, self.expr.exp).evaluate()
            if self.expr_lt_modulus:
                possible_ret_vals.append(new_expr)
            possible_ret_vals.append(Mod(new_expr, self.modulus))

        if isinstance(self.expr, (Mul, Add)):
            cls = self.expr.__class__
            new_expr_args = []
            for t in self.expr.args:
                new_t_expr = Mod(t, self.modulus).evaluate()

                # TODO: new_t_expr.modulus == self.modulus should be True,
                # but verifying here
                if isinstance(new_t_expr, Mod) and new_t_expr.modulus == self.modulus:
                    new_t_expr = new_t_expr.expr
                if new_t_expr == Constant(0) and cls is Mul:
                    return Constant(0)
                new_expr_args.append(new_t_expr)
            new_expr = cls(*new_expr_args).evaluate()
            if self.expr_lt_modulus:
                possible_ret_vals.append(new_expr)
            # no evaluate here, base case since all sub mods should
            # have been fully evaluated
            possible_ret_vals.append(Mod(new_expr, self.modulus))

        if isinstance(self.expr, (Sum, Prod)):
            if not self.expr.sequence.is_finite:  # has length
                return self
            if (
                isinstance(self.expr, Prod)
                and isinstance(self.modulus, SequenceTerm)
                and self.modulus.sequence == self.expr.sequence
            ):
                return Constant(0)

            from pylogic.proposition.relation.contains import IsContainedIn
            from pylogic.structures.set_ import SeqSet

            if (
                isinstance(self.expr, Prod)
                and IsContainedIn(self.modulus, SeqSet(self.expr.sequence))
                in self.modulus.knowledge_base
            ):
                return Constant(0)

            if self.expr.sequence.nth_term is not None:
                n = Variable("mod_dummy_var", integer=True)
                new_nth_term = Mod(
                    self.expr.sequence.nth_term(n), self.modulus
                ).evaluate()

                # TODO: new_t_expr.modulus == self.modulus should be True,
                # but verifying here
                if (
                    isinstance(new_nth_term, Mod)
                    and new_nth_term.modulus == self.modulus
                ):
                    new_nth_term = new_nth_term.expr
                if new_nth_term == Constant(0):  # true for Sum and Prod
                    return Constant(0)
                new_sequence = self.expr.sequence.__class__(
                    name=f"{self.expr.sequence.name} mod {self.modulus}",
                    nth_term=lambda ind: new_nth_term.replace({n: ind}),
                    integer=True,
                    length=self.expr.sequence.length,
                )
                if self.expr_lt_modulus:
                    possible_ret_vals.append(self.expr.__class__(new_sequence))
                possible_ret_vals.append(
                    Mod(self.expr.__class__(new_sequence), self.modulus)
                )

        # if not returned at this point
        if len(possible_ret_vals) == 0 and self.expr_lt_modulus:
            return self.expr
        if len(possible_ret_vals) == 0 and not self.expr_lt_modulus:
            return self

        # looks funny, but we return the value with the shortest string representation
        possible_ret_vals.append(self)
        ret_val = min(possible_ret_vals, key=lambda x: len(str(x)))
        if isinstance(ret_val, Mod) and ret_val.expr != self.expr:
            # hopefuly this does not cause infinite recursion
            return ret_val.evaluate()
        return ret_val

    def to_sympy(self) -> sp.Basic:
        return sp.Mod(self.expr.to_sympy(), self.modulus.to_sympy())

    def _latex(self) -> str:
        from pylogic.enviroment_settings.settings import settings

        if settings["SHOW_ALL_PARENTHESES"]:
            wrap = lambda p: (
                rf"\left({p._latex()}\right)" if not p.is_atomic else p._latex()
            )
        else:
            wrap = lambda p: (
                rf"\left({p._latex()}\right)"
                if not p.is_atomic
                and not p._is_wrapped
                and p.__class__._precedence >= self.__class__._precedence
                else p._latex()
            )
        return "\\mod ".join(map(wrap, self.args))

    def __str__(self) -> str:
        from pylogic.enviroment_settings.settings import settings

        if settings["SHOW_ALL_PARENTHESES"]:
            wrap = lambda p: f"({p})" if not p.is_atomic else str(p)
        else:
            wrap = lambda p: (
                f"({p})"
                if not p.is_atomic
                and not p._is_wrapped
                and p.__class__._precedence >= self.__class__._precedence
                else str(p)
            )
        return " mod ".join(map(wrap, self.args))
