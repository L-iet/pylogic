from pylogic import *
from pylogic.proposition.proof_search import proof_search

A = propositions("A", is_assumption=True)
B, C, D, E, F, G = propositions("B", "C", "D", "E", "F", "G")
p6 = Implies(And(Or(D, E), Or(A, F)), G, is_assumption=True)
A_imp_B = Implies(A, B, is_assumption=True)
B_imp_C = Implies(B, C, is_assumption=True)
C_imp_D = Implies(C, D, is_assumption=True)
kb = [
    # A,
    B.or_(C).assume(),
    # A_imp_B,
    # B_imp_C,
    B.implies(F).assume(),
    # C_imp_D,
    C.implies(G).assume(),
    # p6,
]
target = F.or_(C)
proof = proof_search(kb, target)
print(proof)
