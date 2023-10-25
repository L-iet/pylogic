class Proposition:
    def __init__(
        self, name: str, is_assumption: bool = False, _is_proven: bool = False
    ) -> None:
        self.name = name
        self.is_assumption = is_assumption
        self._is_proven = _is_proven

    def __eq__(self, other: "Proposition") -> bool:
        return self.name == other.name

    def __repr__(self) -> str:
        return self.name

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
        other: Implies
            Must be an implication that has been proven whose structure is
            {self.name} -> OtherProposition
        """
        assert self.is_proven, f"{self.name} is not proven"
        assert other.is_proven, f"{other.name} is not proven"
        assert other.antecendent == self, f"{other.name} does not imply {self.name}"
        return Proposition(other.consequent.name, _is_proven=True)


class Not(Proposition):
    def __init__(self, negating: Proposition, is_assumption: bool = False) -> None:
        self.negating = negating
        name = rf"~[{negating.name}]"
        super().__init__(name, is_assumption)

    def copy(self) -> "Not":
        return Not(self.negating.copy(), self.is_assumption)


class Implies(Proposition):
    def __init__(
        self,
        antecedent: Proposition,
        consequent: Proposition,
        is_assumption: bool = False,
    ) -> None:
        self.antecendent = antecedent
        self.consequent = consequent
        name = f"{antecedent.name} -> {consequent.name}"
        super().__init__(name, is_assumption)

    def copy(self) -> "Implies":
        return Implies(
            self.antecendent.copy(), self.consequent.copy(), self.is_assumption
        )

    def hypothetical_syllogism(self, other: "Implies") -> "Implies":
        """
        Logical tactic.
        """
        assert self.is_proven, f"{self.name} is not proven"
        assert other.is_proven, f"{other.name} is not proven"
        assert (
            self.consequent == other.antecendent
        ), f"Does not follow logically: {self.name},  {other.name}"
        i = Implies(self.antecendent, other.consequent)
        i._is_proven = True
        return i


class And(Proposition):
    def __init__(
        self,
        *propositions: Proposition,
        is_assumption: bool = False,
    ) -> None:
        self.propositions = propositions
        name = rf" /\ ".join([p.name for p in propositions])
        super().__init__(name, is_assumption)

    def __contains__(self, other: Proposition) -> Proposition:
        f"""
        Logical Tactic.
        If we have proven {self.name}, we can prove any of the propositions in it.
        """
        assert self.is_proven, f"{self.name} is not proven"
        assert other in self.propositions, f"{other.name} is not in {self.name}"
        other = other.copy()
        other._is_proven = True
        return other


class Or(Proposition):
    def __init__(
        self,
        *propositions: Proposition,
        is_assumption: bool = False,
    ) -> None:
        self.propositions = propositions
        name = rf" \/ ".join([p.name for p in propositions])
        super().__init__(name, is_assumption)


if __name__ == "__main__":
    p = Proposition
    P = p("P")
    Q = p("Q")
    R = p("R")
    S = p("S")

    PImpQ = P.implies(Q, is_assumption=True)
    P.is_assumption = True
