import sympy as sp


class Variable(sp.Symbol):
    def __repr__(self):
        return super().__repr__()


Var = Variable
