from pylogic.proposition.proposition import Proposition
from pylogic.proposition.implies import Implies
from pylogic.proposition.quantified.forall import Forall
from pylogic.proposition.quantified.exists import Exists
from pylogic.proposition.not_ import neg
from pylogic.proposition.or_ import Or
from pylogic.proposition.and_ import And
from pylogic.variable import Variable
from pylogic.proposition.proof_search import proof_search

Prop = Proposition

# Case 1
# we need to set all the predicates that will
# be in the KB as assumptions.
P = Prop("P", is_assumption=True)
Q = Prop("Q", True)
R = Prop("R", True)
S = Prop("S", True)
T = Prop("T")
PImpQ = Implies(P, Q, True)
QImpR = Q.implies(R, True)  # another way to get an implication
RImpS = Implies(R, S, True)
SImpT = Implies(S, T, True)

print("Case 1")
inf_res1 = proof_search([P, PImpQ, QImpR, RImpS, SImpT], T)
print(inf_res1, end="\n\n")
# (InfResult(InfResult(InfResult(P, [P -> Q], 'modus_ponens', Q), [Q -> R],
#                   'modus_ponens', R), [R -> S], 'modus_ponens', S), [S -> T], 'modus_ponens', T)


# Case 2
print("Case 2")
SImpNotT = S.implies(neg(T), True)
QImpT = Q.implies(T, True)
inf_res2 = proof_search([S, PImpQ, QImpT, RImpS, SImpNotT], neg(P))
print(inf_res2, end="\n\n")
# (InfResult(InfResult(S, [S -> ~T], 'modus_ponens', ~T), [Q -> T],
#          'modus_tollens', ~Q), [P -> Q], 'modus_tollens', ~P)


x = Variable("x")
y = Variable("y")
Px = Prop("P", args=[x])
Py = Prop("P", args=[y])
Qx = Prop("Q", args=[x])
Rx = Prop("R", args=[x])
Sx = Prop("S", args=[x])
prem1 = Forall(x, Px, is_assumption=True)
prem2 = Forall(x, Implies(Px, Qx), True)
prem3 = Forall(x, Qx.implies(Rx), True)
prem4 = Exists(x, Px.implies(Sx), True)
fxRx = Forall(x, Rx)
exSx = Exists(x, Sx)

# Case 3
print("Case 3")
inf_res3 = proof_search([prem1, prem2, prem3, prem4], exSx)
print(inf_res3, end="\n\n")
# (forall x: P (x,), exists x: [P (x,) -> S (x,)], 'quantified_modus_ponens', exists x: S (x,))

# Case 4
print("Case 4")
inf_res4 = proof_search([prem1, prem2, prem3, prem4], Prop("R", args=[10]))
print(inf_res4, end="\n\n")
# (InfResult(InfResult(forall x: P (x,), forall x: [P (x,) -> Q (x,)],
#                   'quantified_modus_ponens', forall x: Q (x,)), forall x: [Q (x,) -> R (x,)],
#       'quantified_modus_ponens', forall x: R (x,)), 'is_special_case_of', R (10,))


# Case 5
print("Case 5")
PandQandRImpS = And(P, Q, R).implies(S, True)
inf_res5 = proof_search([R, Q, P, PandQandRImpS], S)
print(inf_res5, end="\n\n")
# (R, InfResult(InfResult([(P /\ Q /\ R) -> S], Q, 'definite_clause_resolve',
#   [(P /\ R) -> S]), R, 'definite_clause_resolve', [P -> S]), 'modus_ponens', S)

# Case 6
print("Case 6")
prem = Forall(x, Exists(y, Py).implies(Qx))
inf_res6 = proof_search([prem, Prop("P", args=[10])], Prop("Q", args=[1]))
print(inf_res6)  # None
