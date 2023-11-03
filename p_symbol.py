import sympy as sp


class Arbitrary:
    _is_arbitrary: bool = True

    @property
    def is_arbitrary(self) -> bool:
        return self._is_arbitrary


class Symbol(sp.Symbol, Arbitrary):
    def __repr__(self):
        return super().__repr__()


class Function(sp.Function, Arbitrary):
    def __repr__(self):
        return super().__repr__()


class MatrixSymbol(sp.MatrixSymbol, Arbitrary):
    def __repr__(self):
        return super().__repr__()
