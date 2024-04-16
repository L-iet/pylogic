from __future__ import annotations
import sympy as sp


class Variable(sp.Symbol):
    def __repr__(self):
        return super().__repr__()

    def copy(self) -> Variable:
        return Variable(self.name)


Var = Variable
