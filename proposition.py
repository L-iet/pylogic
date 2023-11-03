from typing import Self
from sympy import (
    Interval,
    Set as SympySet,
    FiniteSet as SympyFiniteSet,
    S as sympy_S,
    Rational,
    var,
    symbols,
)
import sympy as sp
import copy
import p_symbol as ps

SympyExpression = sp.Basic | int | float

####################################################


class Set:
    _is_arbitrary: bool = True

    @property
    def is_arbitrary(self) -> bool:
        return self._is_arbitrary

    def __init__(self, sympy_set: SympySet, name: str | None = None):
        if name:
            name = name.strip()
        else:
            name = ""
        assert " " not in name, "Set name cannot contain spaces"
        self.name = name or str(sympy_set)
        self.sympy_set = sympy_set

    def __eq__(self, other: "ArgValueTypes") -> bool:
        return self.name == str(other)

    def contains(
        self, other: "SympyExpression | Set", is_assumption: bool = False
    ) -> "Proposition":
        return Contains(self, other, is_assumption=is_assumption)

    def __repr__(self) -> str:
        return self.name

    def __copy__(self) -> "Set":
        return self.copy()

    def copy(self) -> "Set":
        return Set(self.sympy_set, self.name)


class Arbitrary:
    def __init__(self, instance: SympyExpression | Set):
        self.instance = instance

    def __eq__(self, other) -> bool:
        return False


class Specific:
    def __init__(self, instance: SympyExpression | Set, prop: "Proposition"):
        self.instance = instance
        self.proposition = prop

    def __eq__(self, other: "Specific") -> bool:
        return self.instance == other.instance and self.proposition == other.proposition


#####################################################

ArgTypes = type[Set] | type[SympyExpression]
ArgValueTypes = Set | SympyExpression


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
            typically Set or SympyExpression instances.
        show_arg_position_names: bool
            Whether to show the argument position identifiers in the __repr__.
            This is useful for propositions with multiple arguments of the same type.
            In p(completed_args={x:x1, y:x2}), the argument position identifiers are x and y.
            If this is False, the __repr__ will be p x1 x2.
            If this is True, the __repr__ will be p x=x1 y=x2.
        """
        completed_args = completed_args or {}
        if len(completed_args) == 0:
            completed_args_order = []
        elif completed_args_order is None or len(completed_args_order) == 0:
            completed_args_order = sorted(list(completed_args.keys()))
        completed_args = {k: completed_args[k] for k in completed_args_order}
        name = name.strip()
        assert set(name.split("_")) != {""}, "Proposition name cannot be empty"
        self.name = name
        self.show_arg_position_names = show_arg_position_names
        self.is_assumption = is_assumption
        self.completed_args = completed_args
        self.completed_args_order = completed_args_order
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

    def __copy__(self) -> "Proposition":
        return self.copy()

    @property
    def is_proven(self) -> bool:
        return self._is_proven or self.is_assumption

    def copy(self) -> "Proposition":
        return Proposition(
            self.name,
            self.is_assumption,
            completed_args=self.completed_args.copy(),
            completed_args_order=self.completed_args_order.copy(),
            show_arg_position_names=self.show_arg_position_names,
            _is_proven=self.is_proven,
        )

    def replace(self, current_val: ArgValueTypes, new_val: ArgValueTypes) -> Self:
        new_p = self.copy()
        for arg_id in new_p.completed_args:
            if new_p.completed_args[arg_id] == current_val:
                new_p.completed_args[arg_id] = new_val
        new_p._is_proven = False
        return new_p

    def implies(
        self,
        other: "Proposition",
        is_assumption: bool = False,
    ) -> "Implies":
        return Implies(self, other, is_assumption)

    def and_(
        self,
        *others: "Proposition",
        is_assumption: bool = False,
    ) -> "And":
        return And(self, *others, is_assumption=is_assumption)

    def p_and(self, *others: "Proposition") -> "And":
        """Logical tactic.
        Same as and_, but returns a proven proposition when self and all others are proven.
        """
        assert len(others) > 0, "Must provide at least one proposition"
        assert self.is_proven, f"{self} is not proven"
        for o in others:
            assert o.is_proven, f"{o} is not proven"
        new_p = self.and_(*others)
        new_p._is_proven = True
        return new_p

    def modus_ponens(self, other: "Implies") -> "Proposition":
        """
        Logical tactic.
        other: Implies
            Must be an implication that has been proven whose structure is
            self.name -> OtherProposition
        """
        assert self.is_proven, f"{self.name} is not proven"
        assert other.is_proven, f"{other.name} is not proven"
        assert other.antecedent == self, f"{other.name} does not imply {self.name}"
        new_p = other.consequent.copy()
        new_p._is_proven = True
        return new_p

    def is_one_of(self, other: "And", _recursive: bool = False) -> Self:
        r"""
        Logical tactic.
        If we have proven other, we can prove any of the propositions in it.
        other: And
            Must be an And that has been proven whose structure is
            self /\ OtherProposition
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

    def is_special_case_of(self, other: "Forall") -> Self:
        """
        Logical tactic.
        other: Proposition
            A proven forall proposition that implies this proposition.
        """
        assert isinstance(other, Forall), f"{other} is not a forall statement"
        assert other.is_proven, f"{other} is not proven"
        assert (
            self.name == other.inner_proposition.name
        ), f"{self} is not a special case of {other}"
        for arg_id in self.completed_args:
            if arg_id in other.completed_args:
                assert type(self.completed_args[arg_id]) == type(
                    other.completed_args[arg_id]
                ), f"{self} is not a special case of {other}: {arg_id} is not the same type"
            else:
                raise ValueError(
                    f"{self} is not a special case of {other}: {arg_id} is not in the completed arguments of {other}"
                )
        new_p = self.copy()
        new_p._is_proven = True
        return new_p

    def followed_from(self, *assumptions: "Proposition") -> "Implies":
        """
        Logical tactic.
        Given self is proven, return a new proposition that is an implication of the form
        assumptions -> self.
        *assumptions: Proposition
            Propositions that implied this proposition.
        This function only accepts propositions that were explicitly declared as assumptions.
        """
        assert self.is_proven, f"{self} is not proven"
        assert len(assumptions) > 0, "Must provide at least one other assumption"
        for a in assumptions:
            assert a.is_assumption, f"{a} is not an assumption"
        if len(assumptions) == 1:
            new_p = assumptions[0].implies(self)
        else:
            new_p = And(*assumptions).implies(self)
        new_p._is_proven = True
        return new_p

    def thus_there_exists(
        self, existential_var: str, expression_to_replace: ArgValueTypes
    ) -> "Exists":
        """
        Logical tactic.
        Given self is proven, return a new proposition that there exists an existential_var such that
        self is true, when self is expressed in terms of that existential_var.
        For example, if self is x^2 + x > 0, existential_var is y and expression_to_replace is x^2, then
        we return the proven proposition Exists y: y + x > 0.

        All occurences of the expression will be replaced according to sympy.subs.

        existential_var: str
            A new variable that is introduced into our new existential proposition.
        expression_to_replace: ArgValueTypes
            An expression that is replaced by the new variable.
        """
        assert self.is_proven, f"{self} is not proven"

        new_p = Exists(
            existential_var_name=existential_var,
            inner_proposition=self,
            expression_to_replace=expression_to_replace,
            _is_proven=True,
        )
        return new_p

    def thus_forall(self, quantified_arg: Set | sp.Basic) -> "Forall":
        """
        Logical tactic.
        Given self is proven, return a new proposition that for all variables, self is true.
        """
        assert self.is_proven, f"{self} is not proven"
        assert quantified_arg.is_arbitrary, f"{quantified_arg} is not arbitrary"
        new_p = Forall(
            inner_proposition=self,
            quantified_arg=quantified_arg,
            _is_proven=True,
        )
        return new_p


class Not(Proposition):
    def __init__(self, negated: Proposition, is_assumption: bool = False) -> None:
        self.negated = negated
        name = rf"~[{negated.name}]"
        super().__init__(name, is_assumption)

    def copy(self) -> "Not":
        return Not(self.negated.copy(), self.is_assumption)


class Implies(Proposition):
    # TODO: Implement __eq__ for Implies, And, Or, Forall, Contains, Relation, Equals etc
    def __init__(
        self,
        antecedent: Proposition,
        consequent: Proposition,
        is_assumption: bool = False,
        _is_proven: bool = False,
    ) -> None:
        self.antecedent = antecedent
        self.consequent = consequent
        name = f"{antecedent.name} -> {consequent.name}"
        super().__init__(name, is_assumption, _is_proven=_is_proven)
        self.completed_args = getattr(self.antecedent, "completed_args", {}).copy()
        self.completed_args.update(getattr(self.consequent, "completed_args", {}))
        self.completed_args_order = getattr(
            self.antecedent, "completed_args_order", []
        ).copy()
        self.completed_args_order.extend(
            getattr(self.consequent, "completed_args_order", [])
        )

    def __repr__(self) -> str:
        return f"[{self.antecedent} -> {self.consequent}]"

    def copy(self) -> "Implies":
        return Implies(
            self.antecedent.copy(),
            self.consequent.copy(),
            self.is_assumption,
            _is_proven=self.is_proven,
        )

    def replace(self, current_val: ArgValueTypes, new_val: ArgValueTypes) -> "Implies":
        new_p = self.copy()
        new_p.antecedent = new_p.antecedent.replace(current_val, new_val)
        new_p.consequent = new_p.consequent.replace(current_val, new_val)
        new_p._is_proven = False
        return new_p

    def hypothetical_syllogism(self, other: "Implies") -> "Implies":
        """
        Logical tactic.
        """
        assert self.is_proven, f"{self} is not proven"
        assert other.is_proven, f"{other} is not proven"
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
        _is_proven: bool = False,
    ) -> None:
        assert len(propositions) > 1, "'And' must have at least two propositions"
        completed_args = {}  # TODO: Figure out completed_args for And, Or, Implies
        self.propositions = propositions
        name = rf" /\ ".join([p.name for p in propositions])
        super().__init__(name, is_assumption, _is_proven=_is_proven)

    def copy(self) -> "And":
        return And(
            *[p.copy() for p in self.propositions],
            is_assumption=self.is_assumption,
            _is_proven=self.is_proven,
        )

    def replace(self, current_val: ArgValueTypes, new_val: ArgValueTypes) -> "And":
        new_p = self.copy()
        new_p.propositions = [
            p.replace(current_val, new_val) for p in new_p.propositions
        ]
        new_p._is_proven = False
        return new_p

    def __repr__(self) -> str:
        s = r" /\ ".join([p.__repr__() for p in self.propositions])
        return f"({s})"


class Or(Proposition):
    def __init__(
        self,
        *propositions: Proposition,
        is_assumption: bool = False,
    ) -> None:
        assert len(propositions) > 1, "'Or' must have at least two propositions"
        self.propositions = propositions
        name = r" \/ ".join([p.name for p in propositions])
        super().__init__(name, is_assumption)

    def copy(self) -> "Or":
        return Or(
            *[p.copy() for p in self.propositions], is_assumption=self.is_assumption
        )

    def replace(self, current_val: ArgValueTypes, new_val: ArgValueTypes) -> "Or":
        new_p = self.copy()
        new_p.propositions = [
            p.replace(current_val, new_val) for p in new_p.propositions
        ]
        new_p._is_proven = False
        return new_p

    def __repr__(self) -> str:
        s = r" \/ ".join([p.__repr__() for p in self.propositions])
        return f"({s})"


class _Quantified(Proposition):
    def __init__(
        self,
        _q: str,
        inner_proposition: Proposition,
        is_assumption: bool = False,
        quantified_arg: tuple[str, ArgValueTypes] | None = None,
        show_arg_position_names: bool = False,
        _is_proven: bool = False,
    ) -> None:
        assert quantified_arg is not None, f"{self} must have a quantified arg"
        super().__init__(
            f"{_q} {quantified_arg[1]}: {inner_proposition.name}",
            is_assumption,
            completed_args=inner_proposition.completed_args,
            completed_args_order=inner_proposition.completed_args_order,
            show_arg_position_names=show_arg_position_names,
            _is_proven=_is_proven,
        )
        self.inner_proposition = inner_proposition
        self.quantified_arg = quantified_arg
        self._q = _q

    def __repr__(self) -> str:
        return f"{self._q} {self.quantified_arg[1]}: {self.inner_proposition}"

    @classmethod
    def copy(cls, instance) -> Self:
        return cls(
            instance.inner_proposition.copy(),
            instance.is_assumption,
            instance.quantified_arg,
            instance.show_arg_position_names,
            instance.is_proven,
        )

    def replace(self, current_val: ArgValueTypes, new_val: ArgValueTypes) -> Self:
        new_p = self.copy()
        new_p.inner_proposition = new_p.inner_proposition.replace(current_val, new_val)
        if new_p.quantified_arg[1] == current_val:
            new_p.quantified_arg = (new_p.quantified_arg[0], new_val)
        new_p._is_proven = False
        return new_p


class Forall(_Quantified):
    def __init__(
        self,
        inner_proposition: Proposition,
        quantified_arg: Set | SympyExpression,
        is_assumption: bool = False,
        show_arg_position_names: bool = False,
        _is_proven: bool = False,
    ) -> None:
        q_arg = ("arg0", quantified_arg)
        super().__init__(
            "forall",
            inner_proposition,
            is_assumption,
            quantified_arg=q_arg,
            show_arg_position_names=show_arg_position_names,
            _is_proven=_is_proven,
        )
        self.quantified_arg_value = self.quantified_arg[1]

    def copy(self):
        return super().copy(self)


class Exists(_Quantified):
    def __init__(
        self,
        inner_proposition: Proposition,
        existential_var_name: str,
        expression_to_replace: ArgValueTypes,
        existential_var_type: type[Set] | type[sp.Basic] = ps.Symbol,
        is_assumption: bool = False,
        show_arg_position_names: bool = False,
        _is_proven: bool = False,
    ) -> None:
        if existential_var_type in [ps.Symbol, ps.Function, ps.MatrixSymbol]:
            is_real = (
                isinstance(expression_to_replace, int)
                or isinstance(expression_to_replace, float)
                or expression_to_replace.is_real
            )
            existential_var = existential_var_type(existential_var_name, real=is_real)  # type: ignore
            existential_var._is_arbitrary = False  # type: ignore
        else:
            # Set
            existential_var = Set(sp.Set(existential_var_name))
            existential_var._is_arbitrary = False
        inner_proposition = inner_proposition.replace(
            expression_to_replace, existential_var
        )
        quantified_arg = ("arg0", existential_var)
        super().__init__(
            "exists",
            inner_proposition,
            is_assumption,
            quantified_arg,
            show_arg_position_names,
            _is_proven,
        )
        self.existential_var = existential_var

    def __iter__(self):
        return iter((self.existential_var, self.inner_proposition))

    def copy(self):
        return super().copy(self)


class Contains(Proposition):
    def __init__(
        self,
        set_: Set,
        element: SympyExpression | Set,
        is_assumption: bool = False,
        show_arg_position_names: bool = False,
        _is_proven: bool = False,
    ) -> None:
        self.set_: Set = set_
        self.element: SympyExpression | Set = element
        name = rf"Contains"
        super().__init__(
            name,
            is_assumption,
            completed_args={"set": set_, "element": element},
            show_arg_position_names=show_arg_position_names,
            _is_proven=_is_proven,
        )

    def __repr__(self) -> str:
        return f"{self.element} in {self.set_}"

    def copy(self) -> "Contains":
        return Contains(
            self.set_.copy(),
            copy.copy(self.element),
            is_assumption=self.is_assumption,
            _is_proven=self.is_proven,
        )

    def replace(self, current_val: ArgValueTypes, new_val: ArgValueTypes) -> "Contains":
        new_p = self.copy()
        if new_p.set_ == current_val:
            new_p.set_ = new_val
        if new_p.element == current_val:
            new_p.element = new_val
        return Contains(
            new_p.set_,
            new_p.element,
            is_assumption=self.is_assumption,
            show_arg_position_names=self.show_arg_position_names,
            _is_proven=False,
        )


class Relation(Proposition):
    def __init__(
        self,
        name: str,
        completed_args: dict[str, ArgValueTypes],
        is_assumption: bool = False,
        show_arg_position_names: bool = False,
        _is_proven: bool = False,
    ) -> None:
        assert len(completed_args) > 1, "Relation must have at least two arguments"
        super().__init__(
            name,
            is_assumption,
            completed_args=completed_args,
            show_arg_position_names=show_arg_position_names,
            _is_proven=_is_proven,
        )

    def __repr__(self) -> str:
        return super().__repr__()

    def copy(self) -> "Relation":
        return Relation(
            self.name,
            completed_args=self.completed_args.copy(),
            is_assumption=self.is_assumption,
            show_arg_position_names=self.show_arg_position_names,
            _is_proven=self.is_proven,
        )

    def replace(self, current_val: ArgValueTypes, new_val: ArgValueTypes) -> "Relation":
        new_p = self.copy()
        new_p.completed_args = {
            k: new_val if v == current_val else v
            for k, v in new_p.completed_args.items()
        }
        return Relation(
            new_p.name,
            completed_args=new_p.completed_args,
            is_assumption=self.is_assumption,
            show_arg_position_names=self.show_arg_position_names,
            _is_proven=False,
        )


class Equals(Relation):
    def __init__(
        self,
        left: ArgValueTypes,
        right: ArgValueTypes,
        is_assumption: bool = False,
        _is_proven: bool = False,
    ) -> None:
        name = "Equals"
        super().__init__(
            name,
            completed_args={"left": left, "right": right},
            is_assumption=is_assumption,
            show_arg_position_names=False,
            _is_proven=_is_proven,
        )
        self.left: ArgValueTypes = left
        self.right: ArgValueTypes = right

    def __repr__(self) -> str:
        return f"{self.completed_args['left']} = {self.completed_args['right']}"

    def copy(self) -> "Equals":
        return Equals(
            copy.copy(self.left),
            copy.copy(self.right),
            is_assumption=self.is_assumption,
            _is_proven=self.is_proven,
        )

    def replace(self, current_val: ArgValueTypes, new_val: ArgValueTypes) -> "Equals":
        new_p = self.copy()
        if new_p.left == current_val:
            new_p.left = new_val
        if new_p.right == current_val:
            new_p.right = new_val
        return Equals(
            new_p.left,
            new_p.right,
            is_assumption=self.is_assumption,
            _is_proven=False,
        )

    def by_simplification(self):
        """Logical tactic."""
        proven = False
        if self.completed_args["left"] == self.completed_args["right"]:
            proven = True
        elif isinstance(self.completed_args["left"], sp.Basic):
            if self.completed_args["left"].equals(self.completed_args["right"]):
                proven = True
        elif isinstance(self.completed_args["right"], sp.Basic):
            if self.completed_args["right"].equals(self.completed_args["left"]):
                proven = True
        if proven:
            new_p = self.copy()
            new_p._is_proven = True
            return new_p
        else:
            raise ValueError(f"{self} cannot be proven by simplification")


class _Ordering:
    @classmethod
    def _multiply_by(
        cls,
        instance: "GreaterThan | LessThan",
        x: SympyExpression,
        p: "GreaterThan | LessThan",
        _sign: str = "positive",
    ) -> "GreaterThan | LessThan":
        assert p.is_proven, f"{p} is not proven"
        if (_sign == "positive" and isinstance(p, LessThan)) or (
            _sign == "negative" and isinstance(p, GreaterThan)
        ):
            assert p.left == 0 and p.right == x, f"{p} does not say that {x} is {_sign}"
        elif (_sign == "positive" and isinstance(p, GreaterThan)) or (
            _sign == "negative" and isinstance(p, LessThan)
        ):
            assert p.left == x and p.right == 0, f"{p} does not say that {x} is {_sign}"
        if _sign == "positive":
            new_p = cls(x * instance.left, x * instance.right)  # type: ignore
        elif _sign == "negative":
            new_p = cls(x * instance.right, x * instance.left)  # type: ignore
        else:
            raise ValueError(f"Invalid sign: {_sign}")
        return new_p

    @classmethod
    def _mul(
        cls, instance: "GreaterThan | LessThan", other: SympyExpression
    ) -> "LessThan":
        if isinstance(other, int) or isinstance(other, float):
            sign = "positive" if other > 0 else "negative"
            proof = (
                GreaterThan(other, 0, _is_proven=True)
                if sign == "positive"
                else LessThan(other, 0, _is_proven=True)
            )
            return cls._multiply_by(instance, other, proof, _sign=sign)  # type: ignore
        else:
            raise ValueError(
                f"Cannot multiply {instance} by {other}, use multiply_by_positive or multiply_by_negative"
            )


class GreaterThan(Relation, _Ordering):
    @staticmethod
    def is_absolute(expr: SympyExpression) -> "GreaterThan":
        """Logical tactic.
        Given an expr of the form sympy.Abs(x), return a proven proposition that says
        sympy.Abs(x) > 0
        """
        assert isinstance(expr, sp.Abs), f"{expr} is not an absolute value"
        return GreaterThan(expr, 0, _is_proven=True)

    @staticmethod
    def is_even_power(expr: SympyExpression) -> "GreaterThan":
        """Logical tactic.
        Given an expr of the form x**(2n), return a proven proposition that says
        x**(2n) > 0
        """
        assert isinstance(expr, sp.Pow), f"{expr} is not a power"
        assert expr.base.is_real, f"{expr.base} is not a real number"
        assert sp.ask(sp.Q.even(expr.exp)), f"{expr} is not a square or even power"
        return GreaterThan(expr, 0, _is_proven=True)

    @staticmethod
    def is_rational_power(
        expr: SympyExpression, proof_base_is_positive: "GreaterThan"
    ) -> "GreaterThan":
        """Logical tactic.
        Given an expr of the form x**(p/q) and a proof that x > 0,
        return a proven proposition that says
        x**(p/q) > 0
        """
        assert isinstance(expr, sp.Pow), f"{expr} is not a power"
        assert expr.base.is_real, f"{expr.base} is not a real number"
        assert (
            proof_base_is_positive.is_proven
        ), f"{proof_base_is_positive} is not proven"
        assert isinstance(
            proof_base_is_positive, GreaterThan
        ), f"{proof_base_is_positive} is not a GreaterThan"
        assert (
            proof_base_is_positive.left == expr.base
            and proof_base_is_positive.right == 0
        ), f"{proof_base_is_positive} does not say that {expr.base} is positive"
        assert sp.ask(sp.Q.rational(expr.exp)), f"{expr} is not a rational power"
        return GreaterThan(expr, 0, _is_proven=True)

    def __init__(
        self,
        left: SympyExpression,
        right: SympyExpression,
        is_assumption: bool = False,
        _is_proven: bool = False,
    ) -> None:
        name = "GreaterThan"
        if (left - right).is_positive is False and (is_assumption or _is_proven):
            raise ValueError(f"Some assumptions in {left}, {right} are contradictory")
        super().__init__(
            name,
            completed_args={"left": left, "right": right},
            is_assumption=is_assumption,
            show_arg_position_names=False,
            _is_proven=_is_proven,
        )
        self.left: SympyExpression = left
        self.right: SympyExpression = right

    def __repr__(self) -> str:
        return f"{self.completed_args['left']} > {self.completed_args['right']}"

    def copy(self) -> "GreaterThan":
        return GreaterThan(
            self.left,
            self.right,
            self.is_assumption,
            _is_proven=self.is_proven,
        )

    def replace(
        self, current_val: SympyExpression, new_val: SympyExpression
    ) -> "GreaterThan":
        new_p = self.copy()
        if new_p.left == current_val:
            new_p.left = new_val
        if new_p.right == current_val:
            new_p.right = new_val
        return GreaterThan(
            new_p.left,
            new_p.right,
            is_assumption=self.is_assumption,
            _is_proven=False,
        )

    def to_positive_inequality(self):
        """If self is of the form a > b, returns an inequality of the form a - b > 0"""
        return GreaterThan(self.left - self.right, sympy_S.Zero)

    def to_negative_inequality(self):
        """If self is of the form a > b, returns an inequality of the form b - a < 0"""
        return LessThan(self.right - self.left, sympy_S.Zero)

    def multiply_by_positive(
        self, x: SympyExpression, proof_x_is_positive: "GreaterThan | LessThan"
    ) -> "GreaterThan":
        return super()._multiply_by(self, x, proof_x_is_positive, _sign="positive")  # type: ignore

    def multiply_by_negative(
        self, x: SympyExpression, proof_x_is_negative: "GreaterThan | LessThan"
    ) -> "GreaterThan":
        return super()._multiply_by(self, x, proof_x_is_negative, _sign="negative")

    def p_multiply_by_positive(
        self, x: SympyExpression, proof_x_is_positive: "GreaterThan | LessThan"
    ) -> "GreaterThan":
        """Logical tactic.
        Same as multiply_by_positive, but returns a proven proposition"""
        assert self.is_proven, f"{self} is not proven"
        new_p = self.multiply_by_positive(x, proof_x_is_positive)
        new_p._is_proven = True
        return new_p

    def p_multiply_by_negative(
        self, x: SympyExpression, proof_x_is_negative: "GreaterThan | LessThan"
    ) -> "GreaterThan":
        """Logical tactic.
        Same as multiply_by_negative, but returns a proven proposition"""
        assert self.is_proven, f"{self} is not proven"
        new_p = self.multiply_by_negative(x, proof_x_is_negative)
        new_p._is_proven = True
        return new_p

    def mul_inverse(self):
        return GreaterThan(
            1 / self.right, 1 / self.left, is_assumption=self.is_assumption
        )

    def to_less_than(self):
        """If self is of the form a > b, returns an inequality of the form b < a"""
        return LessThan(self.right, self.left, is_assumption=self.is_assumption)

    def p_to_less_than(self):
        """Logical tactic. Same as to_less_than, but returns a proven proposition"""
        assert self.is_proven, f"{self} is not proven"
        new_p = self.to_less_than()
        new_p._is_proven = True
        return new_p

    def __mul__(self, other: SympyExpression) -> "GreaterThan":
        return super()._mul(self, other)

    def __rmul__(self, other: SympyExpression) -> "GreaterThan":
        return super()._mul(self, other)


class LessThan(Relation, _Ordering):
    def __init__(
        self,
        left: SympyExpression,
        right: SympyExpression,
        is_assumption: bool = False,
        _is_proven: bool = False,
    ) -> None:
        name = "LessThan"
        if (right - left).is_positive is False and (is_assumption or _is_proven):
            raise ValueError(f"Some assumptions in {left}, {right} are contradictory")
        super().__init__(
            name,
            completed_args={"left": left, "right": right},
            is_assumption=is_assumption,
            show_arg_position_names=False,
            _is_proven=_is_proven,
        )
        self.left: SympyExpression = left
        self.right: SympyExpression = right

    def __repr__(self) -> str:
        return f"{self.completed_args['left']} < {self.completed_args['right']}"

    def copy(self) -> "LessThan":
        return LessThan(
            self.left,
            self.right,
            self.is_assumption,
            _is_proven=self.is_proven,
        )

    def replace(
        self, current_val: SympyExpression, new_val: SympyExpression
    ) -> "LessThan":
        new_p = self.copy()
        if new_p.left == current_val:
            new_p.left = new_val
        if new_p.right == current_val:
            new_p.right = new_val
        return LessThan(
            new_p.left,
            new_p.right,
            is_assumption=self.is_assumption,
            _is_proven=False,
        )

    def to_positive_inequality(self):
        """If self is of the form a < b, returns an inequality of the form b - a > 0"""
        return GreaterThan(self.right - self.left, sympy_S.Zero)

    def to_negative_inequality(self):
        """If self is of the form a < b, returns an inequality of the form a - b < 0"""
        return LessThan(self.left - self.right, sympy_S.Zero)

    def multiply_by_positive(
        self, x: SympyExpression, proof_x_is_positive: "GreaterThan | LessThan"
    ) -> "LessThan":
        return super()._multiply_by(self, x, proof_x_is_positive, _sign="positive")  # type: ignore

    def multiply_by_negative(
        self, x: SympyExpression, proof_x_is_negative: "GreaterThan | LessThan"
    ) -> "LessThan":
        return super()._multiply_by(self, x, proof_x_is_negative, _sign="negative")

    def p_multiply_by_positive(
        self, x: SympyExpression, proof_x_is_positive: "GreaterThan | LessThan"
    ) -> "LessThan":
        """Logical tactic.
        Same as multiply_by_positive, but returns a proven proposition"""
        assert self.is_proven, f"{self} is not proven"
        new_p = self.multiply_by_positive(x, proof_x_is_positive)
        new_p._is_proven = True
        return new_p

    def p_multiply_by_negative(
        self, x: SympyExpression, proof_x_is_negative: "GreaterThan | LessThan"
    ) -> "LessThan":
        """Logical tactic.
        Same as multiply_by_negative, but returns a proven proposition"""
        assert self.is_proven, f"{self} is not proven"
        new_p = self.multiply_by_negative(x, proof_x_is_negative)
        new_p._is_proven = True
        return new_p

    def mul_inverse(self):
        return LessThan(1 / self.right, 1 / self.left, is_assumption=self.is_assumption)

    def to_greater_than(self):
        """If self is of the form a < b, returns an inequality of the form b > a"""
        return GreaterThan(self.right, self.left, is_assumption=self.is_assumption)

    def p_to_greater_than(self):
        """Logical tactic. Same as to_greater_than, but returns a proven proposition"""
        assert self.is_proven, f"{self} is not proven"
        new_p = self.to_greater_than()
        new_p._is_proven = True
        return new_p

    def transitive(self, other: "LessThan") -> "LessThan":
        """Logical Tactic. If self is of the form a < b and other is of the form b < c,
        returns a proven inequality of the form a < c.
        """
        assert self.is_proven, f"{self} is not proven"
        assert other.is_proven, f"{other} is not proven"
        assert isinstance(other, LessThan), f"{other} is not a LessThan"
        assert (
            self.right == other.left
        ), f"{self} and {other} do not fulfill transitivity"
        new_p = LessThan(self.left, other.right)
        new_p._is_proven = True
        return new_p

    def __mul__(self, other: SympyExpression) -> "LessThan":
        return super()._mul(self, other)

    def __rmul__(self, other: SympyExpression) -> "LessThan":
        return super()._mul(self, other)


if __name__ == "__main__":
    p = Proposition
    Px = p("P", completed_args={"arg1": ps.Symbol("x")})
    Py = p("P", completed_args={"arg1": ps.Symbol("y")})
    Q = p("Q")
    R = p("R")
    S = p("S")
    T = p("T")
    forallXPx = Forall(Px, quantified_arg=ps.Symbol("x"), is_assumption=True)

    # print(Py, forallXPx)
    py = Py.is_special_case_of(forallXPx)
    # print(py.is_proven)

    x = ps.Symbol("x", real=True)
    eps = ps.Symbol("eps", real=True)
    eps_positive = GreaterThan(eps, 0, is_assumption=True)
    absolute_x_positive = GreaterThan.is_absolute(sp.Abs(x))
    root_eps_positive = GreaterThan.is_rational_power(sp.sqrt(eps), eps_positive)
    absx_lt_sqrt_eps = LessThan(sp.Abs(x), sp.sqrt(eps), is_assumption=True)
    xsq_lt_eps_t_absx = absx_lt_sqrt_eps.p_multiply_by_positive(
        abs(x), GreaterThan.is_absolute(abs(x))
    )
    eps_t_absx_lt_eps = absx_lt_sqrt_eps.p_multiply_by_positive(
        sp.sqrt(eps), root_eps_positive
    )
    xsq_lt_eps = xsq_lt_eps_t_absx.transitive(eps_t_absx_lt_eps)
    x_squared_is_continuous = (
        (root_eps_positive.p_and((xsq_lt_eps).followed_from(absx_lt_sqrt_eps)))
        .thus_there_exists("delta", sp.sqrt(eps))
        .followed_from(eps_positive)
        .thus_forall(eps)
        .thus_forall(x)
    )

    # TODO
    # Option 1: Implement a way to determine what equations need to hold for two propositions
    # to be equivalent

    print(x_squared_is_continuous, x_squared_is_continuous.is_proven)
