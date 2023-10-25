from typing import Any
from set import Set, Object
from proposition import Proposition


ArgTypes = type[Set] | type[Object]
ArgValueTypes = Set | Object


class Predicate:
    def __new__(
        cls,
        name: str,
        args: dict[str, ArgTypes] = {},
    ) -> "Predicate | Proposition":
        if len(args) == 0:
            return Proposition(name)
        return super().__new__(cls)

    def __init__(
        self,
        name: str,
        args: dict[str, ArgTypes],
    ) -> None:
        self.name = name
        self.args = args
        self.args_order = sorted(args.keys())
        self.arg_values: dict[str, ArgValueTypes] = {}

    def __call__(self, **kwds: ArgValueTypes) -> "Predicate | Proposition":
        if len(kwds) == 0:
            return self
        # construct a new predicate with name indicating the filled arguments
        filled_args: str = ""
        for argument in kwds:
            if argument in self.args:
                assert isinstance(
                    kwds[argument], self.args[argument]
                ), f"Used wrong type for argument {argument}\nGot {type(kwds[argument])}\nExpected {self.args[argument]}"
                filled_args += f"{argument}={kwds[argument]} "
        filled_args = filled_args.strip()
        new_args = {k: v for k, v in self.args.items() if k not in kwds}
        new_name = f"{self.name} {filled_args}"
        new_name = new_name.strip()
        return Predicate(new_name, new_args)

    def __repr__(self) -> str:
        s = "_ " * len(self.args_order)
        s = s.strip()
        return f"{self.name} {s}"

    def __eq__(self, other: "Predicate") -> bool:
        self_name_parts = self.name.split()
        other_name_parts = other.name.split()
        self_name_parts.sort()
        other_name_parts.sort()
        return self_name_parts == other_name_parts and self.args == other.args

    def show_args(self):
        for arg in self.args_order:
            print(f"{arg}: {self.args[arg]}", end=" ")
        print()


if __name__ == "__main__":
    p = Predicate("p", {"X": Set, "y": Object})
    s1 = Set("S1")
    o1 = Object("o1")
    print(p())
    print(((p(X=s1, y=o1)).__repr__()).__repr__())
