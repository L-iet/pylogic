from pylogic.theories.real_analysis import *
from pylogic.proposition.proposition import Proposition

printing = True

axioms: list[Proposition] = [
    add_assoc,
    add_comm,
    add_inv,
    zero_exists,
    one_exists,
    mul_assoc,
    mul_comm,
    mul_inv,
    distributive,
]

for axiom in axioms:
    print(axiom.describe())
