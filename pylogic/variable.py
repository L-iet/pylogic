from __future__ import annotations
from pylogic.symbol import Symbol


class Variable(Symbol):
    def __init__(self, *args, **kwargs) -> None:
        super().__init__(*args, **kwargs)
        self.is_bound: bool = False

    def unbind(self) -> None:
        self.is_bound = False

    pass


def unbind(*variables: Variable) -> None:
    """Unbinds variables. This indicates that they are no longer bound to a
    quantifier and can be reused in nested quantified statements.
    """
    for variable in variables:
        variable.unbind()


Var = Variable
