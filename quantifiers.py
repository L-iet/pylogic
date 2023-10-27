from predicate import (
    ArgTypes,
    ArgValueTypes,
    Object,
    Predicate,
    Implies,
    And,
    Or,
    Proposition,
    P_Implies,
    P_And,
    P_Or,
    P_Forall,
    p,
)


class Forall(Predicate):
    def __new__(
        cls,
        predicate: Predicate,
        quantified_arg: tuple[str, ArgTypes] = ("arg1", Object),
        quantified_arg_value: ArgValueTypes | None = None,
        show_arg_position_names: bool = False,
    ) -> Predicate | P_Forall:
        if isinstance(predicate, Proposition):
            assert (
                quantified_arg_value is not None
            ), f"Received Proposition {predicate} but no quantified arg_value"
            return P_Forall(
                predicate,
                False,
                (quantified_arg[0], quantified_arg_value),
                show_arg_position_names,
            )
        return object.__new__(cls)

    def __init__(
        self,
        predicate: Predicate,
        quantified_arg: tuple[str, ArgTypes] = ("arg1", Object),
        quantified_arg_value: ArgValueTypes | None = None,
        show_arg_position_names: bool = False,
    ) -> None:
        name = f"forall {quantified_arg_value if quantified_arg_value else '_'}: {predicate.name}"
        args = predicate.args.copy()
        self.predicate = predicate.copy()
        assert (
            quantified_arg[0] in args
        ), f"{predicate} does not have argument id {quantified_arg[0]}"
        super().__init__(name, args)
        self.quantified_arg_id, self.quantified_arg_type = quantified_arg
        self.quantified_arg_value: ArgValueTypes | None = quantified_arg_value
        self.show_arg_position_names = show_arg_position_names

    def __call__(self, **kwds: ArgValueTypes) -> "Forall | Predicate | Proposition":
        if self.quantified_arg_id in kwds and self.quantified_arg_value is None:
            return Forall(
                self.predicate(**kwds),  # type: ignore
                (self.quantified_arg_id, self.quantified_arg_type),
                kwds[self.quantified_arg_id],
                self.show_arg_position_names,
            )
        else:
            new_pred = self.predicate(**kwds)
            if isinstance(new_pred, Predicate):
                return Forall(
                    new_pred,
                    (self.quantified_arg_id, self.quantified_arg_type),
                    self.quantified_arg_value,
                    self.show_arg_position_names,
                )
            else:
                # new_pred is a Proposition, but quantified argument is not filled
                # ideally should never happen
                raise ValueError(
                    f"Quantified argument {self.quantified_arg_id} not filled in {self}\nbut filled in {new_pred}"
                )

    def __repr__(self) -> str:
        return f"forall _: {self.predicate}"


if __name__ == "__main__":
    x = Object("x")
    y = Object("y")
    x0 = Object("x0")
    y0 = Object("y0")
    x1 = Object("x1")
    y1 = Object("y1")
    z = Object("z")
    P = Predicate("P", {"arg1": Object})
    Q = Predicate("Q", {"arg1": Object})

    P_ImplyQ_ = Implies(P, Q)
    forall___P_ImplyQ_ = Forall(P_ImplyQ_)
    filled = forall___P_ImplyQ_(arg1=x)  # forall x: P x -> Q x
    filled.is_assumption = True
    # Px0ImpQx0 = P_ImplyQ_(arg1=x0)
    Px0ImpQx0 = Implies(P(arg1=x0), Q(arg1=x0))
    Px0 = P(arg1=x0)
    Px0.is_assumption = True
    print(
        Px0.modus_ponens((Px0ImpQx0).is_special_case_of(filled)),
    )
