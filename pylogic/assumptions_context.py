from __future__ import annotations

from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from pylogic.proposition.proposition import Proposition
    from pylogic.variable import Variable


class AssumptionsContext:
    def __init__(self):
        self.assumptions: list[Proposition | Variable] = []
        self._proven: list[Proposition] = []  # all props proven inside the context

        # the conclusions to use to build implications
        self._interesting_conclusions: list[Proposition] = []

        # the implications true ourside the context
        self.proven_propositions: list[Proposition] = []
        self.exited = False
        assumptions_contexts.append(self)

    def variable(self, *args, **kwargs) -> Variable:
        from pylogic.variable import Variable

        return Variable(*args, context=self, **kwargs)

    def var(self, *args, **kwargs) -> Variable:
        return self.variable(*args, **kwargs)

    def variables(self, *names: str, **kwargs) -> list[Variable]:
        return [self.variable(name, **kwargs) for name in names]

    def _build_proven(self, conclusion: Proposition) -> Proposition:
        """
        Build the proven implication or Forall proposition that is proven by closing
        all scopes introduced in this context.
        For example, if self.assumptions is
        `[x, x in S, y, P(y), y in T]`, we return
        `forall x in S: forall y: (P(y) and y in T) => conclusion`

        self.assumptions is reversed before calling this method.
        So we essentially loop through self.assumptions in reverse, and at each index:

        - if the item is an IsContainedIn, check if the previous item is the corresponding
        free variable, in which case we build a ForallInSet
        - if the item is a proposition, use that and all propositions before the next
        IsContainedIn/Variable to build an implication
        - if the item is a free variable, build a Forall
        """
        from pylogic.inference import Inference
        from pylogic.proposition.and_ import And
        from pylogic.proposition.contradiction import Contradiction
        from pylogic.proposition.not_ import neg
        from pylogic.proposition.proposition import Proposition, get_assumptions
        from pylogic.proposition.quantified.forall import Forall, ForallInSet
        from pylogic.proposition.relation.contains import IsContainedIn
        from pylogic.variable import Variable

        conclusion._set_is_proven(False)

        i = 0
        cons = conclusion

        # for if we are building an And(...) => cons
        current_ante: list[Proposition] = []

        while i < len(self.assumptions):
            a = self.assumptions[i]
            if (
                i + 1 < len(self.assumptions)
                and (isinstance(a, IsContainedIn))
                and a.left == self.assumptions[i + 1]
                and a.left.is_bound is False
                and len(a.left.depends_on) == 0
            ):
                cons = ForallInSet(a.left, a.right, cons)
                i += 2  # skip the variable
            elif isinstance(a, Proposition):
                current_ante.append(a)  # type: ignore
                j = i + 1
                while j < len(self.assumptions) and not isinstance(
                    self.assumptions[j], (IsContainedIn, Variable)
                ):
                    current_ante.append(self.assumptions[j])  # type: ignore
                    j += 1
                if len(current_ante) == 1:
                    if isinstance(cons, Contradiction):
                        cons = neg(current_ante[0])
                    else:
                        cons = current_ante[0].implies(cons)
                else:
                    current_ante.reverse()
                    if isinstance(cons, Contradiction):
                        cons = neg(And(*current_ante))
                    else:
                        cons = And(*current_ante).implies(cons)
                current_ante = []
                i = j
            else:
                # a is a free Variable, and we didn't skip so use Forall
                if a.is_bound is False and len(a.depends_on) == 0:
                    cons = Forall(a, cons)
                i += 1
        cons._set_is_proven(
            True,
            context=assumptions_contexts[-2] if len(assumptions_contexts) > 1 else None,
        )
        if conclusion.deduced_from is None:
            cons.deduced_from = Inference(conclusion, rule="close_assumptions_context")
        else:
            other_props = tuple(
                filter(
                    lambda x: x is not None,
                    (
                        conclusion.deduced_from.starting_premise,
                        *conclusion.deduced_from.other_premises,
                    ),
                )
            )
            cons.deduced_from = Inference(
                conclusion,  # the conclusion is included first here
                *other_props,
                rule="close_assumptions_context",
            )
        cons.from_assumptions = get_assumptions(conclusion).difference(self.assumptions)
        return cons

    def open(self):
        return self.__enter__()

    def close(self):
        if self.exited:
            return
        return self.__exit__(None, None, None)

    def __enter__(self):
        return self

    def __exit__(self, exc_type, exc_value, traceback):
        if self.exited:
            return
        from pylogic.proposition.proposition import Proposition

        assert (
            self == assumptions_contexts[-1]
        ), "Cannot exit context because a nested (inner) context is still open"

        # these proven props were only true inside the context
        # do these first because the _build_proven method
        # still runs inside the context, and we want those
        # to be True outside the context
        # we don't call _set_is_proven(False) on these because
        # perhaps a copy was proven in an outer context and we don't want to mutate
        # the Terms in the props
        for p in self._proven:
            p._is_proven = False
            p.from_assumptions = set()
            p.deduced_from = None

        self.assumptions.reverse()
        for a in self.assumptions:
            if isinstance(a, Proposition):
                a._set_is_assumption(False)

        for p in self._interesting_conclusions:
            self.proven_propositions.append(self._build_proven(p))
        del assumptions_contexts[-1]
        self.assumptions.reverse()
        self.exited = True

    def get_proven(self):
        if self.exited:
            return self.proven_propositions
        return []


def conclude(conclusion: Proposition) -> Proposition:
    """
    Used inside a context.

    Tell pylogic that you are interested in proving an implication
    or a Forall statement incolving this conclusion when the context is closed.
    """
    assert conclusion.is_proven, f"{conclusion} is not proven"

    if assumptions_contexts[-1] is not None:
        assumptions_contexts[-1]._interesting_conclusions.append(conclusion)
    return conclusion


def context_variable(*args, **kwargs) -> Variable:
    from pylogic.variable import Variable

    return Variable(*args, context=assumptions_contexts[-1], **kwargs)


def ctx_var(*args, **kwargs) -> Variable:
    return context_variable(*args, **kwargs)


def context_variables(*names: str, **kwargs) -> list[Variable]:
    return [context_variable(name, **kwargs) for name in names]


def ctx_vars(*names: str, **kwargs) -> list[Variable]:
    return context_variables(*names, **kwargs)


assumptions_contexts: list[AssumptionsContext | None] = [None]
