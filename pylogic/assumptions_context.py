from __future__ import annotations

from typing import TYPE_CHECKING, overload

if TYPE_CHECKING:
    from pylogic.proposition.proposition import Proposition
    from pylogic.variable import Variable


class AssumptionsContext:
    def __init__(self, name: str | None = None):
        self.name = name
        self.assumptions: list[Proposition | Variable] = []
        self._proven: list[Proposition] = []  # all props proven inside the context

        # the conclusions to use to build implications
        self._interesting_conclusions: list[Proposition] = []

        # the implications true outside the context
        self.proven_propositions: list[Proposition] = []
        self.exited = False
        assumptions_contexts.append(self)

    def __repr__(self):
        return f"AssumptionsContext({self.name})" if self.name else super().__repr__()

    def __str__(self):
        return self.__repr__()

    def variable(self, *args, **kwargs) -> Variable:
        from pylogic.variable import Variable

        return Variable(*args, context=self, **kwargs)

    def var(self, *args, **kwargs) -> Variable:
        return self.variable(*args, **kwargs)

    @overload
    def variables(self, name: str, **kwargs) -> Variable: ...
    @overload
    def variables(self, *names: str, **kwargs) -> tuple[Variable, ...]: ...
    def variables(self, *names: str, **kwargs) -> Variable | tuple[Variable, ...]:
        if len(names) == 1:
            return self.variable(names[0], **kwargs)
        return tuple(self.variable(name, **kwargs) for name in names)

    @overload
    def vars(self, name: str, **kwargs) -> Variable: ...
    @overload
    def vars(*names: str, **kwargs) -> tuple[Variable, ...]: ...
    def vars(self, *names: str, **kwargs) -> Variable | tuple[Variable]:
        return self.variables(*names, **kwargs)

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
        from pylogic.proposition.implies import Implies
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
                        # dont de-nest, to avoid
                        # changing a -> (b -> c) to ((a and b) -> c)
                        cons = current_ante[0].implies(cons, de_nest=False)
                else:
                    current_ante.reverse()
                    if isinstance(cons, Contradiction):
                        cons = neg(And(*current_ante))
                    else:
                        cons = And(*current_ante).implies(cons, de_nest=False)
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
        cons.deduced_from = Inference(
            None,
            conclusion=cons,
            rule="close_assumptions_context",
            inner_contexts=[self],
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
        # still runs inside the context, and we want the results from that
        # to be True outside the context
        # we don't call _set_is_proven(False) on these because
        # perhaps a copy was proven in an outer context and we don't want to mutate
        # the Terms in the props
        # keep the assumptions and deduced_from because they are useful for
        # Inference and reconstructing the proof
        for p in self._proven:
            p._is_proven = False

        self.assumptions.reverse()
        for a in self.assumptions:
            if isinstance(a, Proposition):
                a._set_is_assumption(False)

        # remove need to call conclude
        if len(self._interesting_conclusions) == 0 and len(self._proven) > 0:
            self.proven_propositions.append(self._build_proven(self._proven[-1]))

        for p in self._interesting_conclusions:
            self.proven_propositions.append(self._build_proven(p))
        del assumptions_contexts[-1]
        self.assumptions.reverse()
        self.exited = True

    def get_proven(self):
        """
        Returns a list of implications that have been proven as a result of
        closing this context.

        Example:
        ```
        p = Proposition("p")
        q = Proposition("q")
        r = Proposition("r")
        p_implies_q = p.implies(q).assume()
        q_implies_r = q.implies(r).assume()
        with AssumptionsContext() as ctx:
            p_true = p.assume()
            r_true = p_true.modus_ponens(p_implies_q).modus_ponens(q_implies_r)
            conclude(r_true)
        print(ctx.get_proven())
        ```
        Output:
        ```
        [p -> r]
        ```
        """
        if self.exited:
            return self.proven_propositions
        return []

    def get_first_proven(self) -> Proposition | None:
        """
        Returns the first proven proposition after the context.
        """
        if self.exited:
            return self.proven_propositions[0] if self.proven_propositions else None
        return None


def conclude(conclusion: Proposition) -> Proposition:
    """
    Used inside a context.

    Tell pylogic that you are interested in proving an implication
    or a Forall statement incolving this conclusion when the context is closed.
    """
    assert conclusion.is_proven, f"{conclusion} is not proven"

    if assumptions_contexts[-1] is not None:
        assumptions_contexts[-1]._interesting_conclusions.append(conclusion)

    # check if conclusion is an assumption so we can update target if needed
    # for eg in proving p -> (q -> p)
    global _target_to_prove
    if conclusion.is_assumption and conclusion == _target_to_prove:
        _target_to_prove = None

    return conclusion


def context_variable(*args, **kwargs) -> Variable:
    from pylogic.variable import Variable

    return Variable(*args, context=assumptions_contexts[-1], **kwargs)


def ctx_var(*args, **kwargs) -> Variable:
    return context_variable(*args, **kwargs)


@overload
def context_variables(name: str, **kwargs) -> Variable: ...
@overload
def context_variables(*names: str, **kwargs) -> tuple[Variable, ...]: ...
def context_variables(*names: str, **kwargs) -> Variable | tuple[Variable, ...]:
    if len(names) == 1:
        return context_variable(names[0], **kwargs)
    return tuple(context_variable(name, **kwargs) for name in names)


@overload
def ctx_vars(name: str, **kwargs) -> Variable: ...
@overload
def ctx_vars(*names: str, **kwargs) -> tuple[Variable, ...]: ...
def ctx_vars(*names: str, **kwargs) -> Variable | tuple[Variable, ...]:
    return context_variables(*names, **kwargs)


def to_prove(*target: Proposition) -> Proposition | None:
    """
    Set a target proposition to prove.

    When called with no arguments, it returns the current target proposition.
    """
    global _target_to_prove
    if len(target) == 0:
        return _target_to_prove
    if len(target) == 1:
        _target_to_prove = target[0]
        return target[0]
    raise ValueError("to_prove() accepts zero or one argument")


assumptions_contexts: list[AssumptionsContext | None] = [None]
_target_to_prove: Proposition | None = None
