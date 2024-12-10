from __future__ import annotations

from typing import TYPE_CHECKING, Callable, Self, TypeVar, TypeVarTuple, overload

import sympy as sp

from pylogic.expressions.expr import Expr, to_sympy
from pylogic.typing import Term

if TYPE_CHECKING:
    from sympy.core.function import UndefinedFunction

    from pylogic.proposition.proposition import Proposition
    from pylogic.structures.collection import Class
    from pylogic.structures.set_ import Set
    from pylogic.variable import Variable

    P = TypeVar("P", bound=Proposition)
    E = TypeVar("E", bound=Expr)
else:
    P = TypeVar("P")
    E = TypeVar("E")
Ps = TypeVarTuple("Ps")
T = TypeVar("T", bound=Term)

# f = PWFunction(
#     "f",
#     if_(x.equals(0)).then(0),
#     if_(x.equals(1)).then(1),
#     otherwise(self(x - 2) + self(x - 1)),
# )

# f = PWFunction("f")
# f.define(
#     if_(x.equals(0)).then(0),
#     if_(x.equals(1)).then(1),
#     otherwise(f(x - 2) + f(x - 1)),
# )


class SelfFunc(Expr):
    def __init__(self, *args: Term) -> None:
        super().__init__(*args)
        self.name: str | None = None  # to be modified by local context

    def evaluate(self, **kwargs) -> Self:
        return self

    def to_sympy(self) -> UndefinedFunction:
        from pylogic.sympy_helpers import PylSympyFunction

        return PylSympyFunction(
            "SelfFunc",
            _pyl_class=self.__class__,
            _pyl_init_args=self._init_args,
            _pyl_init_kwargs=self._init_kwargs,
        )

    def _latex(self) -> str:
        name = self.name or "self"
        return f"{name}({', '.join(arg._latex() for arg in self.args)})"

    def __str__(self) -> str:
        name = self.name or "self"
        return f"{name}({', '.join(str(arg) for arg in self.args)})"

    def update_properties(self) -> None:
        return


def contains_self(expr: Expr) -> bool:
    """
    Check if an expression contains a SelfFunc.
    """
    if isinstance(expr, SelfFunc):
        return True
    elif not isinstance(expr, Expr):
        return False
    for arg in expr.args:
        if not isinstance(arg, Expr):
            continue
        if contains_self(arg):
            return True
    return False


@overload
def replace_self_func(expr: SelfFunc, func: Callable[[SelfFunc], T]) -> T: ...
@overload
def replace_self_func(expr: E, func: Callable[[SelfFunc], T]) -> E: ...
def replace_self_func(expr: E, func: Callable[[SelfFunc], T]) -> T | E:
    """
    Replace all SelfFuncs in an expression with a Term.
    """
    if isinstance(expr, SelfFunc):
        return func(expr)
    elif not isinstance(expr, Expr):
        return expr
    new_args = [replace_self_func(arg, func) for arg in expr.args]  # type: ignore
    new_expr = expr.copy()
    new_expr._build_args_and_symbols(*new_args)
    return new_expr


class Function(Expr):
    """
    the function's `args` include the domain and codomain.
    """

    # order of operations for expressions (0-indexed)
    # Function MinElement Abs SequenceTerm Pow Prod Mul Sum Add Binary_Expr
    # Custom_Expr Piecewise Relation(eg <, subset)
    _precedence = 0
    _is_wrapped = True

    def __init__(self, *args, **kwargs) -> None:
        super().__init__(*args, **kwargs)
        self.kwargs = self.kwargs + [
            ("domain", "domain"),
            ("codomain", "codomain"),
            ("parameters", "parameters"),
            ("definition", "definition"),
        ]
        self.mutable_attrs_to_copy = self.mutable_attrs_to_copy + ["name"]

    def __new_init__(
        self,
        name: str,
        domain: Set | Variable | Class | None = None,
        codomain: Set | Variable | Class | None = None,
        parameters: tuple[Variable, ...] | None = None,
        definition: Expr | None = None,
    ) -> None:
        from pylogic.enviroment_settings.set_universe import get_universe
        from pylogic.proposition.relation.contains import IsContainedIn
        from pylogic.structures.set_ import (
            CartesPower,
            FiniteCartesProduct,
            UniversalSet,
        )
        from pylogic.variable import Variable

        self.name = name
        self.codomain: Set | Variable | Class = codomain or get_universe()
        self.definition: Expr | None = None
        assert (parameters is None and definition is None) or (
            parameters is not None and definition is not None
        ), "Both parameters and definition must be provided."
        if parameters is not None:
            assert all(
                isinstance(p, Variable) for p in parameters
            ), "All parameters must be Variables."
        self.parameters: tuple[Variable, ...] | None = parameters

        if definition is not None:
            self._validate_and_set_definition(definition)

        # try to infer domain from parameters
        if domain is not None:
            # don't evaluate if passed in explicitly
            self.domain = domain
        elif parameters is not None:
            individual_sets = []
            for p in parameters:
                for prop in p.knowledge_base:
                    if isinstance(prop, IsContainedIn):
                        individual_sets.append(prop.right)
                        break
                else:
                    # we could not find a set for this parameter
                    # so cannot infer the domain at all
                    break
            else:
                # we found sets for all parameters
                if len(set(individual_sets)) == 1:
                    self.domain = CartesPower(
                        individual_sets[0], len(parameters)
                    ).evaluate()
                else:
                    self.domain = FiniteCartesProduct(sets=individual_sets).evaluate()
        else:
            self.domain = get_universe()

        super().__new_init__(self.domain, self.codomain)

        # construct the proposition forall(x, f(x) in codomain)
        if self.codomain != UniversalSet:
            self._construct_forall_proposition(name, parameters=parameters)

        self._init_args = (name,)
        self._init_kwargs = {
            "domain": domain,
            "codomain": codomain,
            "parameters": parameters,
            "definition": definition,
        }

    def _construct_forall_proposition(
        self,
        name: str,
        parameters: tuple[Variable, ...] | None = None,
    ):
        from pylogic.proposition.quantified.forall import Forall, ForallInSet
        from pylogic.proposition.relation.contains import IsContainedIn
        from pylogic.structures.sequence import FiniteSequence
        from pylogic.structures.set_ import (
            CartesPower,
            FiniteCartesProduct,
            UniversalSet,
        )
        from pylogic.variable import Variable

        if parameters is None:
            x = Variable("x")
            if self.domain != UniversalSet:
                self.proposition = ForallInSet(
                    x,
                    self.domain,
                    IsContainedIn(self(x), self.codomain),
                    is_assumption=True,
                )
            else:
                self.proposition = Forall(
                    x,
                    IsContainedIn(self(x), self.codomain),
                    is_assumption=True,
                )
        elif (
            self.domain == UniversalSet
            or isinstance(self.domain, CartesPower)
            or isinstance(self.domain, FiniteCartesProduct)
        ):
            n = len(parameters)
            i = -1
            cur_var = parameters[i]
            if self.domain == UniversalSet:
                forall_class = Forall
                set_sequence = (None,) * n
            elif isinstance(self.domain, CartesPower):
                forall_class = ForallInSet
                set_sequence = (self.domain.base_set,) * n
            else:
                # isinstance(self.domain, FiniteCartesProduct)
                forall_class = ForallInSet
                set_sequence: tuple[Set | Variable, ...] | tuple[None, ...] = self.domain.set_tuple  # type: ignore
            cur_prop = forall_class(
                variable=cur_var,
                set_=set_sequence[i],
                inner_proposition=IsContainedIn(self(*parameters), self.codomain),
            )
            for i in range(n - 2, -1, -1):
                cur_var = parameters[i]
                cur_prop = forall_class(
                    variable=cur_var,
                    set_=set_sequence[i],
                    inner_proposition=cur_prop,
                )
            self.proposition: Forall = cur_prop
        else:
            # given parameters but domain is not a Cartesian product or UniversalSet
            n = len(parameters)
            i = -1
            cur_var = parameters[i]
            cur_prop = Forall(
                variable=cur_var,
                inner_proposition=FiniteSequence(
                    f"{name}_args", length=n, initial_terms=parameters
                )
                .is_in(self.domain)
                .implies(IsContainedIn(self(*parameters), self.codomain)),
            )
            for i in range(n - 2, -1, -1):
                cur_var = parameters[i]
                cur_prop = Forall(
                    variable=cur_var,
                    inner_proposition=cur_prop,
                )
            self.proposition: Forall = cur_prop
        self.proposition.is_assumption = True
        self.knowledge_base.add(self.proposition)

    def evaluate(self, **kwargs) -> Self:
        return self

    def to_sympy(self) -> UndefinedFunction:
        from pylogic.sympy_helpers import PylSympyFunction

        return PylSympyFunction(
            self.name,
            _pyl_class=self.__class__,
            _pyl_init_args=self._init_args,
            _pyl_init_kwargs=self._init_kwargs,
        )

    def _latex(self) -> str:
        return rf"{self.name}: {self.domain._latex()} \to {self.codomain._latex()}"

    def __str__(self) -> str:
        return f"{self.name}: {self.domain} -> {self.codomain}"

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, Function):
            return NotImplemented
        return (
            self.name == other.name
            and self.domain == other.domain
            and self.codomain == other.codomain
        )

    def __hash__(self) -> int:
        return hash((self.name, self.domain, self.codomain))

    def _validate_and_set_definition(self, definition: Expr) -> None:
        if isinstance(definition, CalledFunction):
            assert (
                definition.function != self
            ), "Cannot define a function in terms of itself."
        definition = replace_self_func(definition, lambda s: self(*s.args))
        self.definition = definition

    def define(self, parameters: tuple[Variable, ...], definition: Expr) -> None:
        self.parameters = parameters
        self._validate_and_set_definition(definition)

    def __call__(self, *args: Term) -> CalledFunction:
        from pylogic.helpers import is_integer_numeric, python_to_pylogic
        from pylogic.structures.sequence import FiniteSequence
        from pylogic.structures.set_ import CartesPower, FiniteCartesProduct

        assert len(args) > 0, "At least one argument must be provided."
        args = tuple(map(python_to_pylogic, args))

        if len(args) == 1:
            if isinstance(args[0], tuple):
                args = args[0]
            elif isinstance(args[0], FiniteSequence):
                args = tuple(args[0].initial_terms)  # type: ignore

        # find the length of an arbitrary n-tuple element of the domain
        if self.parameters is not None:
            n = len(self.parameters)
        elif isinstance(self.domain, CartesPower):
            if is_integer_numeric(self.domain.power):
                n = int(self.domain.power)  # type: ignore
        elif isinstance(self.domain, FiniteCartesProduct):
            n = len(self.domain.sets)
        else:
            n = 1
        assert len(args) in [
            n,
            1,
        ], f"Number of arguments does not match domain structure, expected {n} but got {len(args)}\nDomain: {self.domain}"

        # I removed the requirement that the arguments must be in the domain
        # because we should be able to do sth like x = Variable("x"); ForallInSet(x, domain, f(x) == y)
        return CalledFunction(self, args)

    def update_properties(self) -> None:
        return


class CalledFunction(Expr):
    _is_wrapped = True

    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.mutable_attrs_to_copy = self.mutable_attrs_to_copy + [
            "function",
            "arguments",
            "replace_dict",
            "all_args_in_domain",
            "add_result_to_codomain",
        ]

    def __new_init__(
        self,
        function: Function,
        arguments: tuple[Term, ...],
    ) -> None:
        from pylogic.inference import Inference
        from pylogic.proposition.relation.contains import IsContainedIn
        from pylogic.structures.sequence import FiniteSequence
        from pylogic.structures.set_ import (
            CartesPower,
            FiniteCartesProduct,
            UniversalSet,
        )

        self.function = function
        self.arguments = arguments
        self.replace_dict: dict[Term, Term]
        if self.function.parameters is None:
            self.replace_dict = {}
        else:
            self.replace_dict = dict(zip(self.function.parameters, arguments))
        super().__new_init__(function, *arguments)

        # check if the arguments are in the domain
        domain = self.function.domain
        all_args_in_domain = False
        set_of_args = set(arguments)
        if domain == UniversalSet:
            all_args_in_domain = True
        elif isinstance(domain, CartesPower):
            all_args_in_domain = (
                all(
                    IsContainedIn(arg, domain.base_set) in arg.knowledge_base
                    for arg in arguments
                )
                if len(arguments) > 1
                else IsContainedIn(arguments[0], domain) in arguments[0].knowledge_base
            )
        elif isinstance(domain, FiniteCartesProduct):
            all_args_in_domain = (
                all(
                    IsContainedIn(arg, domain.set_tuple[i]) in arg.knowledge_base
                    for i, arg in enumerate(arguments)
                )
                if len(arguments) > 1
                else IsContainedIn(arguments[0], domain) in arguments[0].knowledge_base
            )
        elif len(arguments) == 1:
            all_args_in_domain = (
                IsContainedIn(arguments[0], domain) in arguments[0].knowledge_base
            )
        else:
            # domain is some other set not a Cartesian product or UniversalSet
            # TODO: test length here to verify it makes sense
            all_args_in_domain = (
                (
                    FiniteSequence(
                        f"{function.name}_args",
                        length=len(arguments),
                        initial_terms=arguments,
                    ).is_in(domain)
                    in arguments[0].knowledge_base
                )
                if len(arguments) > 1
                else IsContainedIn(arguments[0], domain) in arguments[0].knowledge_base
            )
        all_kb = set()
        for arg in arguments:
            all_kb.update(arg.knowledge_base)
        other_premises: list[IsContainedIn] = list(
            filter(
                lambda p: isinstance(p, IsContainedIn) and p.left in set_of_args, all_kb
            )
        )
        if all_args_in_domain and self.function.codomain != UniversalSet:
            self.knowledge_base.add(
                IsContainedIn(
                    self,
                    self.function.codomain,
                    _is_proven=True,
                    _assumptions=self.function.knowledge_base,
                    _inference=Inference(
                        self.function.proposition, *other_premises, rule="function_application"  # type: ignore
                    ),
                )
            )
        self.all_args_in_domain = all_args_in_domain
        self.add_result_to_codomain = (
            all_args_in_domain and self.function.codomain != UniversalSet
        )

        # TODO: computation to update `is_real`, `is_rational` etc.

        self._init_args = (function, arguments)
        self._init_kwargs = {}

    def evaluate(self, **kwargs) -> Term:
        from pylogic.inference import Inference
        from pylogic.proposition.relation.contains import IsContainedIn

        if self.function.definition is None:
            return self
        res = self.function.definition.replace(self.replace_dict)
        if res is not self and self.add_result_to_codomain:
            res.knowledge_base.add(
                IsContainedIn(
                    res,
                    self.function.codomain,
                    _is_proven=True,
                    _assumptions=self.function.knowledge_base,
                    # TODO: this is missing other_premises
                    _inference=Inference(
                        self.function.proposition, rule="function_application"
                    ),
                )
            )
        return res

    def to_sympy(self) -> sp.Basic:
        return self.function.to_sympy()(*[arg.to_sympy() for arg in self.arguments])  # type: ignore

    def _latex(self) -> str:
        return rf"{self.function.name}\left({', '.join(arg._latex() for arg in self.arguments)}\right)"

    def __str__(self) -> str:
        return f"{self.function.name}({', '.join(str(arg) for arg in self.arguments)})"

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, CalledFunction):
            return NotImplemented
        return self.function == other.function and self.arguments == other.arguments

    def __hash__(self) -> int:
        return hash(
            (
                self.function.name,
                self.function.domain,
                self.function.codomain,
                *self.arguments,
            )
        )

    def update_properties(self) -> None:
        return


self = SelfFunc
