from pylogic.proposition.proposition import Proposition


class Not(Proposition):
    def __init__(self, negated: Proposition, is_assumption: bool = False) -> None:
        self.negated = negated
        name = rf"~{negated.name}"
        super().__init__(name, is_assumption)

    def copy(self) -> "Not":
        return Not(self.negated.copy(), self.is_assumption)
