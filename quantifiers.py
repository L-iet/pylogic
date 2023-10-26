from predicate import (
    ArgTypes,
    ArgValueTypes,
    Object,
    Predicate,
    Proposition,
    P_Implies,
    P_And,
    P_Or,
    p,
)


class Forall(Predicate):
    def __new__(cls, predicate: Predicate, arg_name: str = "x") -> Predicate:
        return object.__new__(cls)

    def __init__(self, predicate: Predicate, arg_name: str = "x") -> None:
        name = f"forall _: {predicate.name}"
        args = predicate.args.copy()
        self.predicate = predicate
        assert arg_name in args, f"{predicate} does not have argument {arg_name}"
        super().__init__(name, args)
        self.quantified_arg_id: str = arg_name

    def __call__(self, **kwds: ArgValueTypes) -> "Forall | Predicate | Proposition":
        if self.quantified_arg_id in kwds:
            new_pred_name = f"forall {kwds[self.quantified_arg_id]}: "
            new_pred_name += self.predicate.name
            new_pred = Predicate(
                new_pred_name,
                self.predicate.args.copy(),
                _quantified_arg=(self.quantified_arg_id, kwds[self.quantified_arg_id]),
            )(**kwds)
            return new_pred
        else:
            new_pred = self.predicate(**kwds)
            if isinstance(new_pred, Predicate):
                return Forall(new_pred, self.quantified_arg_id)
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
    p = Predicate("P", {"arg1": Object})
    fp = Forall(p, "arg1")
    forallxPx = fp(arg1=x)
    print(forallxPx, forallxPx.completed_args)
