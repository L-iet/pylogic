from pylogic import *
from pylogic.proposition.proof_search import proof_search


def test1():
    A = propositions("A", is_assumption=True)
    B, C, D, E, F, G = propositions("B", "C", "D", "E", "F", "G")
    p6 = Implies(And(Or(D, E), Or(A, F)), G, is_assumption=True)
    A_imp_B = Implies(A, B, is_assumption=True)
    B_imp_C = Implies(B, C, is_assumption=True)
    C_imp_D = Implies(C, D, is_assumption=True)
    kb = [
        # A,
        # A_imp_B,
        # B_imp_C,
        # C_imp_D,
        C.implies(G).assume(),
        B.implies(F).assume(),
        B.or_(C).assume(),
        # p6,
    ]
    target = F.or_(C)
    proof = proof_search(kb, target)
    print(proof)


def test2():
    P, Q, R, S = propositions("P", "Q", "R", "S")

    p1 = neg(P.and_(Q.or_(R, S)))  # .assume()
    p2 = neg(P).or_(neg(Q).and_(neg(R), neg(S))).assume()

    kb = [
        p2,
    ]

    target = p1
    proof = proof_search(kb, target)
    print(proof.deduced_from)


def test3():
    I, J, K, M, N = propositions("I", "J", "K", "M", "N")
    p1 = I.implies(J).assume()
    p2 = J.or_(I, K).assume()
    p3 = J.implies(M).assume()
    p4 = neg(M).assume()
    p5 = K.implies(neg(N)).assume()

    target = neg(N)
    kb = [
        p1,
        p2,
        p3,
        p4,
        p5,
    ]

    proof = proof_search(kb, target)
    print(proof.deduced_from)


test3()
