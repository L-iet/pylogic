from __future__ import annotations

from typing import TYPE_CHECKING

from pylogic.assumptions_context import AssumptionsContext, conclude
from pylogic.inference import Inference
from pylogic.proposition.and_ import And
from pylogic.proposition.contradiction import Contradiction
from pylogic.proposition.iff import Iff
from pylogic.proposition.implies import Implies
from pylogic.proposition.not_ import Not, are_negs, neg
from pylogic.proposition.or_ import Or
from pylogic.proposition.proposition import Proposition
from pylogic.proposition.relation.equals import Equals


def proof_search(kb: list[Proposition], target: Proposition) -> Proposition:
    """
    Attempt to build an Inference proving `target` from premises in `kb`.
    Raises ValueError if no proof is found.
    """
    return _BackwardProver(kb).prove(target)


def inference(
    *,
    premises: list[Proposition],
    inference_rule_name: str,
    inner_context: AssumptionsContext | None,
    conclusion: Proposition,
) -> Inference:
    """
    Create an Inference object with the given premises, inference rule name,
    inner context, and conclusion.
    """
    return Inference(
        *premises,
        conclusion,
        rule=inference_rule_name,
    )


def conc(inf: Inference) -> Proposition:
    """
    Get the conclusion of an Inference object.
    """
    return inf.other_premises[-1]


def print_kb(kb: list[Proposition]) -> None:
    """
    Print the knowledge base (KB) in a readable format.
    """
    print("-" * 20)
    for p in kb:
        print(p)
    print("\n")


class _BackwardProver:
    def __init__(
        self, kb: list[Proposition], no_extend: set[Proposition] | None = None
    ) -> None:
        # knowledge base of proven propositions
        self.kb = list(kb)  # make copy in case other prover has same kb
        self.no_extend = no_extend.copy() if no_extend else set()
        for p in self.kb:
            if isinstance(p, And) and not p in self.no_extend:
                self.kb.extend(p.extract())
                self.no_extend.add(p)

    def prove(self, goal: Proposition) -> Proposition:
        return self._prove(goal, visited=set(), no_recurse_on=set())

    def _prove(
        self,
        goal: Proposition,
        visited: set,
        no_recurse_on: set[Proposition],
    ) -> Proposition:
        """
        no_recurse_on: propositions that have already been recursed on
        no_extend: conjunctions whose conjuncts have already been added
        to this KB in a higher-up (shallower) recursive call
        """
        visited = visited.copy()
        # detect loops
        if goal in visited:
            raise ValueError(f"Cannot prove {goal} (cycle detected)")
        visited.add(goal)

        # if goal.name == "C":
        #    print(goal, visited, self.kb)

        # by inspection, by evaluation
        try:
            res = goal.by_inspection()
            return res
        except ValueError:
            pass

        # try:
        #     res = self._prove(Contradiction(), visited, no_recurse_on)
        #     return res.ex_falso(goal)  # type:ignore
        # except ValueError:
        #     pass

        # by inspection, by evaluation
        if isinstance(goal, Equals):
            try:
                res = goal.by_eval()
                return res
            except ValueError:
                pass

        for indx in range(len(self.kb) - 1, -1, -1):
            p = self.kb[indx]
            if p == goal:
                return p
            if isinstance(p, Contradiction):
                # if we find a contradiction in KB, we can prove anything
                return p.ex_falso(goal)

            # Conjunction‐elim: if we find in KB some A and B … whose i-th child = goal
            if isinstance(p, And):
                for i, c in enumerate(p.propositions):
                    if c == goal:
                        return p[i]  # proven version of c

            # trying to get Modus Ponens or Modus Tollens
            if isinstance(p, Implies) and p not in no_recurse_on:
                try:
                    ant_inf = self._prove(
                        p.antecedent, visited, no_recurse_on=no_recurse_on.union({p})
                    )
                    cons = ant_inf.modus_ponens(p)
                    if cons == p:
                        continue
                    new_prover = _BackwardProver(
                        self.kb + [cons], no_extend=self.no_extend
                    )
                    ret_val = new_prover._prove(
                        goal, visited=set(), no_recurse_on=no_recurse_on.union({p})
                    )
                    return ret_val
                except ValueError as e:
                    pass
                try:
                    neg_cons_inf = self._prove(
                        neg(p.consequent),
                        visited,
                        no_recurse_on=no_recurse_on.union({p}),
                    )
                    neg_ante = neg_cons_inf.modus_tollens(p)
                    if neg_ante == p:
                        continue
                    # for _i, _p in enumerate(self.kb + [neg_ante]):
                    #     if not _p.is_proven:
                    #         raise Exception(
                    #             f"{_p} at index {_i} is not proven "
                    #             + str(len(self.kb) + 1)
                    #         )
                    new_prover = _BackwardProver(
                        self.kb + [neg_ante], no_extend=self.no_extend
                    )
                    ret_val = new_prover._prove(
                        goal, visited=set(), no_recurse_on=no_recurse_on.union({p})
                    )
                    return ret_val
                except ValueError:
                    pass

            # Proof-by-cases
            # avoid case-splitting on already case-split propositions
            if isinstance(p, Or) and p not in no_recurse_on:
                # print(2, f"Trying to prove {goal} from {p}")
                # print_kb(self.kb)
                contexts: list[AssumptionsContext] = []
                for i, c in enumerate(p.propositions):
                    if TYPE_CHECKING:
                        assert isinstance(c, Proposition)
                    ctx = AssumptionsContext().open()
                    c.assume()
                    # add c to KB only within this context
                    new_prover = _BackwardProver(
                        self.kb + [c], no_extend=self.no_extend
                    )
                    try:
                        new_prover._prove(
                            goal,
                            visited=set(),
                            no_recurse_on=no_recurse_on.union({p}),
                        )  # fresh visited for inner
                        # print(3, f"Goal {goal} proven by case {i} on {p}")
                    except ValueError:
                        # if we cannot prove goal in this case, break
                        # print(4, f"Goal {goal} NOT proven by case {i} on {p}")
                        pass
                    finally:
                        # cleanup
                        ctx.close()
                        # del new_prover # might be needed to avoid
                        # accidentally using it beyond this point
                        break
                    contexts.append(ctx)
                else:
                    # if we get here, we have proven goal in all cases
                    # print(5, f"Goal {goal} proven by cases on {p}")
                    ret_val = goal.copy()
                    ret_val._set_is_proven(True)
                    ret_val.deduced_from = Inference(
                        p,
                        conclusion=ret_val,
                        rule="by_cases",
                        inner_contexts=contexts,
                    )
                    return ret_val

        # Conjunction‐intro: if goal = A ∧ B ∧ …, prove each conjunct
        if isinstance(goal, And):
            sub_infs = [
                self._prove(c, visited, no_recurse_on) for c in goal.propositions
            ]
            conj = sub_infs[0].and_(*sub_infs[1:])  # user‐supplied rule
            return conj

        # Implication‐intro: if goal = A → B, discharge A to prove B
        if isinstance(goal, Implies):
            ctx = AssumptionsContext(auto_conclude=False).open()
            goal.antecedent.assume()
            # add A to KB only within this context
            new_prover = _BackwardProver(
                self.kb + [goal.antecedent], no_extend=self.no_extend
            )
            try:
                b_inf = new_prover._prove(
                    goal.consequent, visited=set(), no_recurse_on=no_recurse_on
                )  # fresh visited for inner
                conclude(b_inf)
            except ValueError:
                pass
            finally:
                # cleanup
                ctx.close()
                # del new_prover # might be needed to avoid
                # accidentally using it beyond this point
            impl = ctx.get_first_proven()
            if impl is None:
                raise ValueError(f"Goal {goal} not proven")
            return impl

        # Disjunction‐intro: if goal is an Or, try to prove at least one side
        if isinstance(goal, Or):
            for side in goal.propositions:
                try:
                    side_inf = self._prove(
                        side, visited=set(), no_recurse_on=no_recurse_on
                    )
                    oi = goal.one_proven(side_inf)  # user‐supplied
                    # print(6, f"Goal {goal} proven by {side} on {goal}")
                    return oi
                except ValueError:
                    # print(7, f"Goal {goal} NOT proven by {side} on {goal}")
                    continue

        # If we get here, no rule applies
        raise ValueError(f"No rule found to prove {goal}")
