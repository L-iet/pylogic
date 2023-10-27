import proposition as p

Proposition = p.Proposition
P_Implies = p.Implies
P_And = p.And
P_Or = p.Or
P_Forall = p.Forall
Set = p.Set
Object = p.Object
ArgTypes = p.ArgTypes
ArgValueTypes = p.ArgValueTypes


class Predicate(p._Statement):
    def __new__(
        cls,
        name: str,
        args: dict[str, ArgTypes] | None = None,
        show_arg_position_names: bool = False,
        _completed_args: dict[str, ArgValueTypes] | None = None,  # compute
        _completed_args_order: list[str] | None = None,  # compute
    ) -> "Predicate | Proposition":
        if args is None or len(args) == 0:
            return Proposition(
                name,
                completed_args=_completed_args,
                completed_args_order=_completed_args_order,
                show_arg_position_names=show_arg_position_names,
            )
        return super().__new__(cls)

    def __init__(
        self,
        name: str,
        args: dict[str, p.ArgTypes],
        show_arg_position_names: bool = False,
        _completed_args: dict[str, ArgValueTypes] | None = None,
        _completed_args_order: list[str] | None = None,
    ) -> None:
        """
        name: str
            Name of the predicate. Typically the first part of the __repr__.
        args: dict[str, ArgTypes]
            Dictionary of argument position identifiers and their types.
        show_arg_position_names: bool
            Whether to show the argument position identifiers in the __repr__.
            This is useful for predicates with multiple arguments of the same type.
            In p(x=x1, y=x2), the argument position identifiers are x and y.
            If this is False, the __repr__ will be p x1 x2.
            If this is True, the __repr__ will be p x=x1 y=x2.
        args_order: list[str]
            List of argument position identifiers in the order they appear in the __repr__.
        arg_values: dict[str, ArgValueTypes]
            Dictionary of argument position identifiers and their values. The values are
            typically Set or Object instances.
        """
        assert set(name.split("_")) != {""}, "Predicate name cannot be empty"
        self.name = name
        self.args = args
        self.args_order = sorted(args.keys())
        self.arg_values: dict[str, ArgValueTypes] = {}
        self.show_arg_position_names: bool = show_arg_position_names
        self._completed_args = _completed_args or {}
        self._completed_args_order = _completed_args_order or []
        assert len(self._completed_args) == len(
            self._completed_args_order
        ), f"Length of completed args and completed args order do not match \
{self._completed_args}\n{self._completed_args_order}"

    def __call__(self, **kwds: ArgValueTypes) -> "Predicate | Proposition":
        if len(kwds) == 0:
            return self
        # construct a new predicate with name indicating the filled arguments
        new_completed_args = self._completed_args.copy()
        new_completed_args_order = self._completed_args_order.copy()
        for argument in self.args_order:
            if argument in kwds:
                assert isinstance(
                    kwds[argument], self.args[argument]
                ), f"Used wrong type for argument {argument}\nGot {type(kwds[argument])}\nExpected {self.args[argument]}"

                new_completed_args[argument] = kwds[argument]
                new_completed_args_order.append(argument)
        new_args = {k: v for k, v in self.args.items() if k not in kwds}
        return Predicate(
            self.name,
            new_args,
            self.show_arg_position_names,
            _completed_args=new_completed_args,
            _completed_args_order=new_completed_args_order,
        )

    def __repr__(self) -> str:
        completed = self.name
        for arg in self._completed_args_order:
            completed += (
                f" {arg}={self._completed_args[arg]}"
                if self.show_arg_position_names
                else f" {self._completed_args[arg]}"
            )

        s = "_ " * len(self.args_order)
        s = s.strip()
        return f"{completed} {s}"

    def __eq__(self, other: "Predicate") -> bool:
        self_name_parts = self.name.split()
        other_name_parts = other.name.split()
        self_name_parts.sort()
        other_name_parts.sort()
        return self_name_parts == other_name_parts and self.args == other.args

    def copy(self) -> "Predicate":
        return Predicate(
            self.name,
            self.args.copy(),
            self.show_arg_position_names,
            self._completed_args.copy(),
            self._completed_args_order.copy(),
        )

    def implies(self, other: "Predicate | Proposition") -> "Implies":
        return Implies(self, other)

    def and_(self, other: "Predicate") -> "And":
        return And(self, other)

    def show_args(self):
        for arg in self.args_order:
            print(f"{arg}: {self.args[arg]}", end=" ")
        print()


class Implies(Predicate):
    def __new__(
        cls,
        antecedent: Predicate | Proposition,
        consequent: Predicate | Proposition,
    ) -> "Predicate | Proposition":
        name = f"{antecedent.name} -> {consequent.name}"
        if isinstance(antecedent, Proposition) and isinstance(consequent, Proposition):
            return P_Implies(antecedent, consequent)
        args = getattr(antecedent, "args", {}).copy()
        args.update(getattr(consequent, "args", {}))
        return super().__new__(cls, name, args)

    def __init__(
        self,
        antecedent: Predicate | Proposition,
        consequent: Predicate | Proposition,
        show_arg_position_names: bool = False,
    ) -> None:
        """If given two propositions, return an Implication Proposition."""
        assert any(
            isinstance(_ent, Predicate) for _ent in (antecedent, consequent)
        ), "At least one argument must be a predicate"
        self.antecedent = antecedent
        self.consequent = consequent
        args = getattr(antecedent, "args", {}).copy()
        args.update(getattr(consequent, "args", {}))
        name = f"{antecedent.name} -> {consequent.name}"
        super().__init__(name, args, show_arg_position_names)
        self.args_order: list[str] = []
        antecedent_args_order = getattr(antecedent, "args_order", [])
        self.args_order.extend(antecedent_args_order)
        consequent_args_order = getattr(consequent, "args_order", [])
        self.args_order.extend(consequent_args_order)

        self._completed_args = getattr(antecedent, "_completed_args", {}).copy()
        self._completed_args.update(getattr(consequent, "_completed_args", {}))
        self._completed_args_order = getattr(
            antecedent, "_completed_args_order", []
        ).copy()
        self._completed_args_order.extend(
            getattr(consequent, "_completed_args_order", [])
        )

    def __call__(self, **kwds: ArgValueTypes) -> "Implies | P_Implies":
        new_antecedent = self.antecedent.copy()
        if isinstance(self.antecedent, Predicate):
            new_antecedent = self.antecedent(**kwds)
        new_consequent = self.consequent.copy()
        if isinstance(self.consequent, Predicate):
            new_consequent = self.consequent(**kwds)
        return Implies(new_antecedent, new_consequent)

    def __repr__(self) -> str:
        return f"{self.antecedent} -> {self.consequent}"

    def copy(self) -> "Implies":
        return Implies(self.antecedent.copy(), self.consequent.copy())


# For now, I'll repeat code for And and Or.
class And(Predicate):
    def __new__(
        cls,
        *predicates: Predicate | Proposition,
    ) -> Predicate | Proposition:
        """
        If given all propositions, return a Conjunction Proposition.
        """
        name = rf" /\ ".join([p.name for p in predicates])
        if all(isinstance(_ent, Proposition) for _ent in predicates):
            return P_And(*predicates)  # type: ignore
        args = {}
        for p in predicates:
            args.update(getattr(p, "args", {}))
        return super().__new__(cls, name, args)

    def __init__(
        self,
        *predicates: Predicate | Proposition,
    ) -> None:
        assert any(
            isinstance(_ent, Predicate) for _ent in predicates
        ), "At least one argument must be a predicate"
        self.predicates = predicates
        name = rf" /\ ".join([p.name for p in predicates])
        args = {}
        for p in predicates:
            args.update(getattr(p, "args", {}))
        super().__init__(name, args)
        self.args_order: list[str] = []
        for p in predicates:
            self.args_order.extend(getattr(p, "args_order", []))

    def __call__(self, **kwds: ArgValueTypes) -> "And | P_And":
        new_predicates = []
        for p in self.predicates:
            new_p = p.copy()
            if isinstance(p, Predicate):
                new_p = p(**kwds)
            new_predicates.append(new_p)
        return And(*new_predicates)

    def __repr__(self) -> str:
        s = ""
        for p in self.predicates:
            s += rf"{p} /\ "
        s = s[:-4]
        return s

    def copy(self) -> "And":
        return And(*[p.copy() for p in self.predicates])


class Or(Predicate):
    def __new__(
        cls,
        *predicates: Predicate | Proposition,
    ) -> Predicate | Proposition:
        """
        If given all propositions, return a Disjunction Proposition.
        """
        name = rf" \/ ".join([p.name for p in predicates])
        if all(isinstance(_ent, Proposition) for _ent in predicates):
            return P_Or(*predicates)  # type: ignore
        args = {}
        for p in predicates:
            args.update(getattr(p, "args", {}))
        return super().__new__(cls, name, args)

    def __init__(
        self,
        *predicates: Predicate | Proposition,
    ) -> None:
        assert any(
            isinstance(_ent, Predicate) for _ent in predicates
        ), "At least one argument must be a predicate"
        self.predicates = predicates
        name = rf" \/ ".join([p.name for p in predicates])
        args = {}
        for p in predicates:
            args.update(getattr(p, "args", {}))
        super().__init__(name, args)
        self.args_order: list[str] = []
        for p in predicates:
            self.args_order.extend(getattr(p, "args_order", []))

    def __call__(self, **kwds: ArgValueTypes) -> "Or | P_Or":
        new_predicates = []
        for p in self.predicates:
            new_p = p.copy()
            if isinstance(p, Predicate):
                new_p = p(**kwds)
            new_predicates.append(new_p)
        return Or(*new_predicates)

    def __repr__(self) -> str:
        s = ""
        for p in self.predicates:
            s += rf"{p} \/ "
        s = s[:-4]
        return s

    def copy(self) -> "Or":
        return Or(*[p.copy() for p in self.predicates])


if __name__ == "__main__":
    p = Predicate("p", {"X": Set, "y": Object})
    q = Predicate("q")
    s1 = Set("S1")
    o1 = Object("o1")
    o2 = Object("o2")
    print(p)  # p _ _
    print(p())  # p _ _
    print(p(X=s1, y=o1))  # p X=S1 y=o1
    print(p(X=s1))  # p X=S1 _

    p2 = Predicate("p2", {"a": Object, "b": Object}, show_arg_position_names=True)
    p3 = Predicate("p3", {"a": Object, "c": Object})
    p2ImpliesP3 = p2.implies(p3)
    print(
        p2ImpliesP3(
            a=o1,
            b=o2,
        )
    )
    p4 = Predicate("p4", {"s": Set, "a": Object})
    conj = And(p2, p3, p4)(a=o1)
    p_ = p2(a=o1, b=o2)
    print(p_)
    print(p2(b=o1)._completed_args_order)
