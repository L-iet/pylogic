from __future__ import annotations
from pylogic.proposition.proposition import Proposition
from typing import TYPE_CHECKING, Self

if TYPE_CHECKING:
    from pylogic.structures.sets import Set
    from pylogic.symbol import Symbol
    from sympy import Basic

    Term = Symbol | Set | Basic | int | float


class Relation(Proposition):
    def __init__(
        self,
        name: str,
        args: list[Term],
        is_assumption: bool = False,
        description: str = "",
        **kwargs,
    ) -> None:
        super().__init__(
            name, is_assumption, description=description, args=args, **kwargs
        )
        self.is_atomic = True

    def __repr__(self) -> str:
        return super().__repr__()

    def __hash__(self) -> int:
        return hash((self.name, tuple(self.args)))

    def as_text(self, *, _indent=0) -> str:
        """
        Return a text representation of the proposition.
        """
        return "  " * _indent + repr(self) + "\n"

    def _latex(self, printer=None) -> str:
        return super()._latex()

    def copy(self) -> Self:
        return self.__class__(
            self.name,
            args=self.args.copy(),
            is_assumption=self.is_assumption,
            description=self.description,
            _is_proven=self._is_proven,
            _assumptions=self.from_assumptions,
            _inference=self.deduced_from,
        )
