from proposition import Proposition


class Object:
    def __init__(self, name: str):
        self.name = name

    def __repr__(self) -> str:
        return self.name


class Set:
    def __init__(self, name: str):
        self.name = name

    def __contains__(self, other: Object) -> Proposition:
        return Proposition(f"{other.name} in {self.name}")

    def __repr__(self) -> str:
        return self.name
