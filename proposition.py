import re

####################################################


class Object:
    def __init__(self, name: str):
        self.name = name

    def __repr__(self) -> str:
        return self.name


class Set:
    def __init__(self, name: str):
        self.name = name

    def __contains__(self, other: Object) -> "Proposition":
        return Proposition(f"{other.name} in {self.name}")

    def __repr__(self) -> str:
        return self.name


#####################################################

ArgTypes = type[Set] | type[Object]
ArgValueTypes = Set | Object


class _Statement:
    name: str
    args: dict[str, ArgTypes] = {}
    args_order: list[str] = []
    arg_values: dict[str, ArgValueTypes] = {}
    is_assumption: bool
    is_proven: bool

    def show_args(self) -> None:
        ...


####################################################


class Proposition(_Statement):
    def __init__(
        self,
        name: str,
        is_assumption: bool = False,
        completed_args: dict[str, ArgValueTypes] | None = None,
        completed_args_order: list[str] | None = None,
        quantified_arg: tuple[str, ArgValueTypes] | None = None,
        show_arg_position_names: bool = False,
        _is_proven: bool = False,
    ) -> None:
        """
        name: str
            Name of the proposition. Typically the first part of the __repr__.
        is_assumption: bool
            Whether this proposition is an assumption.
        completed_args: dict[str, ArgValueTypes]
            Dictionary of argument position identifiers and their values. The values are
            typically Set or Object instances.
        quantified_arg: tuple[str, ArgValueTypes]
            Argument position identifier and its value. The value is typically a Set or Object instance.
        show_arg_position_names: bool
            Whether to show the argument position identifiers in the __repr__.
            This is useful for propositions with multiple arguments of the same type.
            In p(completed_args={x:x1, y:x2}), the argument position identifiers are x and y.
            If this is False, the __repr__ will be p x1 x2.
            If this is True, the __repr__ will be p x=x1 y=x2.
        """
        completed_args = completed_args or {}
        completed_args_order = completed_args_order or []
        name = name.strip()
        self.name = name
        self.show_arg_position_names = show_arg_position_names
        self.is_assumption = is_assumption
        self.completed_args = completed_args
        self.completed_args_order = completed_args_order
        if self.name.startswith("forall") or self.name.startswith("exists"):
            assert quantified_arg is not None, f"{self} must have a quantified arg"
        self.quantified_arg = quantified_arg
        self._is_proven = _is_proven

    def __eq__(self, other: "Proposition") -> bool:
        return self.name == other.name and self.completed_args == other.completed_args

    def __repr__(self) -> str:
        s = ""
        for arg_id in self.completed_args_order:
            s += (
                f"{arg_id}={self.completed_args[arg_id]} "
                if self.show_arg_position_names
                else f"{self.completed_args[arg_id]} "
            )
        return f"{self.name} {s}".strip()

    @property
    def is_proven(self) -> bool:
        return self._is_proven or self.is_assumption

    @is_proven.setter
    def is_proven(self, value: bool) -> None:
        raise ValueError("Cannot set is_proven directly.")

    def copy(self) -> "Proposition":
        return Proposition(self.name, self.is_assumption)

    def implies(self, other: "Proposition", is_assumption: bool = False) -> "Implies":
        return Implies(self, other, is_assumption)

    def and_(self, other: "Proposition", is_assumption: bool = False) -> "And":
        return And(self, other, is_assumption=is_assumption)

    def modus_ponens(self, other: "Implies") -> "Proposition":
        f"""
        Logical tactic.
        other: Implies
            Must be an implication that has been proven whose structure is
            {self.name} -> OtherProposition
        """
        assert self.is_proven, f"{self.name} is not proven"
        assert other.is_proven, f"{other.name} is not proven"
        assert other.antecedent == self, f"{other.name} does not imply {self.name}"
        new_p = other.consequent.copy()
        new_p._is_proven = True
        return new_p

    def is_one_of(self, other: "And", _recursive: bool = False) -> "Proposition":
        rf"""
        Logical tactic.
        If we have proven {other}, we can prove any of the propositions in it.
        other: And
            Must be an And that has been proven whose structure is
            {self} /\ OtherProposition
        """
        if not _recursive:
            assert other.is_proven, f"{other} is not proven"
        for p in other.propositions:
            if p == self:
                new_p = self.copy()
                new_p._is_proven = True
                return new_p
            elif isinstance(p, And):
                try:
                    return self.is_one_of(p, _recursive=True)
                except ValueError:
                    continue
        raise ValueError(f"{self} is not in {other}")


class Not(Proposition):
    def __init__(self, negated: Proposition, is_assumption: bool = False) -> None:
        self.negated = negated
        name = rf"~[{negated.name}]"
        super().__init__(name, is_assumption)

    def copy(self) -> "Not":
        return Not(self.negated.copy(), self.is_assumption)


class Implies(Proposition):
    def __init__(
        self,
        antecedent: Proposition,
        consequent: Proposition,
        is_assumption: bool = False,
    ) -> None:
        self.antecedent = antecedent
        self.consequent = consequent
        name = f"{antecedent.name} -> {consequent.name}"
        super().__init__(name, is_assumption)

    def copy(self) -> "Implies":
        return Implies(
            self.antecedent.copy(), self.consequent.copy(), self.is_assumption
        )

    def hypothetical_syllogism(self, other: "Implies") -> "Implies":
        """
        Logical tactic.
        """
        assert self.is_proven, f"{self.name} is not proven"
        assert other.is_proven, f"{other.name} is not proven"
        assert (
            self.consequent == other.antecedent
        ), f"Does not follow logically: {self.name},  {other.name}"
        i = Implies(self.antecedent, other.consequent)
        i._is_proven = True
        return i


class And(Proposition):
    def __init__(
        self,
        *propositions: Proposition,
        is_assumption: bool = False,
    ) -> None:
        assert len(propositions) > 1, "'And' must have at least two propositions"
        self.propositions = propositions
        name = rf" /\ ".join([p.name for p in propositions])
        super().__init__(name, is_assumption)

    def copy(self) -> "And":
        return And(
            *[p.copy() for p in self.propositions], is_assumption=self.is_assumption
        )


class Or(Proposition):
    def __init__(
        self,
        *propositions: Proposition,
        is_assumption: bool = False,
    ) -> None:
        assert len(propositions) > 1, "'Or' must have at least two propositions"
        self.propositions = propositions
        name = rf" \/ ".join([p.name for p in propositions])
        super().__init__(name, is_assumption)

    def copy(self) -> "Or":
        return Or(
            *[p.copy() for p in self.propositions], is_assumption=self.is_assumption
        )


if __name__ == "__main__":
    p = Proposition
    P = p("P")
    Q = p("Q")
    R = p("R")
    S = p("S")
    T = p("T")

    Ax = p("A", completed_args={"arg1": Object("x")})

    PAndQ = P.and_(Q)
    PAndQ_AndR = PAndQ.and_(R, is_assumption=True)
    P_And_QAndR = P.and_(Q.and_(R))
    proofq: Proposition = Q.is_one_of(PAndQ_AndR)
    print(Ax.is_proven)
