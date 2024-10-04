from __future__ import annotations

from typing import TYPE_CHECKING, Self

from pylogic import Term
from pylogic.proposition.proposition import Proposition


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
        from pylogic.constant import Constant
        from pylogic.expressions.expr import Expr
        from pylogic.structures.set_ import Set
        from pylogic.variable import Variable

        self.is_atomic = True
        self.variables = set()
        self.constants = set()
        self.sets = set()
        self.class_ns = set()
        for arg in self.args:
            if isinstance(arg, Variable):
                self.variables.add(arg)
            elif isinstance(arg, Set):
                self.sets.add(arg)
            elif isinstance(arg, Constant):
                self.constants.add(arg)
            elif isinstance(arg, Expr):
                self.variables.update(arg.variables)
                self.constants.update(arg.constants)
                self.sets.update(arg.sets)
            else:
                cls = arg.__class__.__name__
                if cls.startswith("Collection") and cls[10].isdigit():
                    self.class_ns.add(arg)  # type: ignore

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
            args=self.args,
            is_assumption=self.is_assumption,
            description=self.description,
            _is_proven=self._is_proven,
            _assumptions=self.from_assumptions,
            _inference=self.deduced_from,
        )

    def deepcopy(self) -> Self:
        from pylogic.helpers import deepcopy

        return self.__class__(
            self.name,
            args=[deepcopy(arg) for arg in self.args],
            is_assumption=self.is_assumption,
            description=self.description,
            _is_proven=self._is_proven,
            _assumptions=self.from_assumptions,
            _inference=self.deduced_from,
        )
