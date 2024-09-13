from __future__ import annotations

from typing import TYPE_CHECKING, Any, Callable, Iterable, Literal, TypeVar, overload

from pylogic.structures.collection import Collection

# https://en.wikipedia.org/wiki/Axiom_schema_of_specification#In_Quine's_New_Foundations
# We follow this New Foundations specification where
# we can have a set of all sets, but the argument of the containment function
# or predicate cannot appear on both sides of an IsContainedIn statement,
# avoiding Russell's paradox.
# Note that we can still have sets that contain themselves,
# and (obviously) sets that do not contain themselves.
# We check for this in a Set or Collection{n} instance `S` by checking if
# `S.containment_function(S)` recurses forever
# or if a proposition of the form `Expr(...S...) in Expr(...S...)`
# appears in `S.predicate(S)`
# If an (AttributeError, TypeError, ValueError) occurs during these checks,
# we assume the functions are valid, since it means `S` does not match an
# implicit pattern.

if TYPE_CHECKING:
    from pylogic.proposition.proposition import Proposition
    from pylogic.proposition.relation.contains import IsContainedIn
    from pylogic.proposition.relation.equals import Equals
    from pylogic.structures.collection import Class
    from pylogic.structures.set_ import Set


def class_n_init(
    self,
    name: str,
    elements: Iterable[Any] | None = None,
    containment_function: Callable[[Any], bool] | None = None,
    predicate: Callable[[Any], Proposition] | None = None,
):
    name = name.strip()
    assert " " not in name, "Set name cannot contain spaces"
    self.name = name
    self.elements = set(elements) if elements else set()
    self._containment_function = containment_function
    if illegal_occur_check:
        self.illegal_occur_check(containment_function, predicate)
    self._predicate = predicate


def class_n_repr(self) -> str:
    return f"{self.__class__.__name__}_{self.name}"


def class_n_hash(self) -> int:
    return hash((self.__class__.__name__, self.name, self.containment_function))


def contains(self, other: Any, is_assumption: bool = False, **kwargs) -> IsContainedIn:
    from pylogic.proposition.relation.contains import IsContainedIn

    """elementhood"""

    return IsContainedIn(other, self, is_assumption=is_assumption, **kwargs)


def equals(self, other: Any, **kwargs) -> Equals:
    from pylogic.proposition.relation.equals import Equals

    return Equals(self, other, **kwargs)


def containment_function(self, x: Any) -> bool:
    from pylogic.structures.set_ import Set

    # TODO: Should a Colletion{n} instance contain a Collection{n-2} instance and lower?

    if isinstance(x, Set) or x.__class__.__name__.startswith("Collection"):
        return self.level == x.level + 1 and self._containment_function(x)
    if x in self.elements:
        return True
    elif self._containment_function:
        return self._containment_function(x)
    return False


def predicate(self, x: Any) -> Proposition:
    from pylogic.proposition.relation.contains import IsContainedIn

    if self._predicate is None:
        return IsContainedIn(x, self)
    return self._predicate(x)


def copy(self):
    return self.__class__(
        name=self.name,
        elements=self.elements,
        containment_function=self._containment_function,
        predicate=self.predicate,
    )


def deepcopy(self):
    from pylogic.helpers import deepcopy

    return self.__class__(
        name=self.name,
        elements=[deepcopy(e) for e in self.elements],
        containment_function=self._containment_function,
        predicate=self.predicate,
    )


def illegal_occur_check(
    self,
    containment_function: Callable[[Any], bool] | None = None,
    predicate: Callable[[Any], Proposition] | None = None,
) -> Literal[False]:
    """
    Perform the illegal occurrence check on the containment function and predicate.
    Returns False if no illegal occurrences are found.
    Raises a ValueError if an illegal occurrence is found.

    https://en.wikipedia.org/wiki/Axiom_schema_of_specification#In_Quine%27s_New_Foundations
    We follow this New Foundations specification where
    we can have a set of all sets, but the argument of the containment function
    or predicate cannot appear on both sides of an IsContainedIn statement,
    avoiding Russell's paradox.


    Note that we can still have sets that contain themselves,
    and (obviously) sets that do not contain themselves.


    We check for this in a Set or Collection{n} instance `S` by checking if
    `S.containment_function(S)` recurses forever
    or if a proposition of the form `Expr(...S...) in Expr(...S...)`
    appears in `S.predicate(S)`
    If an (AttributeError, TypeError, ValueError) occurs during these checks,
    we assume the functions are valid, since it means `S` does not match an
    implicit pattern.
    """
    if containment_function is not None:
        try:
            containment_function(self)
        except RecursionError as e:
            raise ValueError(
                "Invalid containment function supplied.\n \
See https://en.wikipedia.org/wiki/Axiom_schema_of_specification#In_Quine%27s_New_Foundations"
            ) from e
        except (AttributeError, TypeError, ValueError):
            pass
    if predicate is not None:
        try:
            illegal_occur = self.illegal_occur_check_pred(predicate(self))
        except (AttributeError, TypeError, ValueError):
            illegal_occur = False
        if illegal_occur:
            raise ValueError(
                "Invalid predicate supplied.\n \
See https://en.wikipedia.org/wiki/Axiom_schema_of_specification#In_Quine%27s_New_Foundations"
            )
    return False


def illegal_occur_check_pred(self, predicate_of_self: Proposition) -> bool:
    from pylogic.helpers import find_first
    from pylogic.proposition._junction import _Junction
    from pylogic.proposition.implies import Implies
    from pylogic.proposition.not_ import Not

    # TODO: Add Iff import
    from pylogic.proposition.quantified.quantified import _Quantified
    from pylogic.proposition.relation.contains import IsContainedIn
    from pylogic.structures.set_ import Set
    from pylogic.symbol import Symbol

    if isinstance(predicate_of_self, IsContainedIn):
        if isinstance(predicate_of_self.left, (Set, Symbol)):
            occurs_in_left = predicate_of_self.left == self
        else:  # Expr
            occurs_in_left = self in predicate_of_self.left.sets
        if isinstance(predicate_of_self.right, (Set, Symbol)):
            occurs_in_right = predicate_of_self.right == self
        else:  # Expr
            occurs_in_right = self in predicate_of_self.right.sets
        return occurs_in_left and occurs_in_right
    elif isinstance(predicate_of_self, Implies):
        return self.illegal_occur_check_pred(
            predicate_of_self.antecedent
        ) or self.illegal_occur_check_pred(predicate_of_self.consequent)
    elif isinstance(predicate_of_self, Not):
        return self.illegal_occur_check_pred(predicate_of_self.negated)
    elif isinstance(predicate_of_self, _Junction):
        return (
            find_first(
                lambda p: self.illegal_occur_check_pred(p),
                predicate_of_self.propositions,
            )[1]
            is not None
        )
    elif isinstance(predicate_of_self, _Quantified):
        return self.illegal_occur_check_pred(predicate_of_self.inner_proposition)
    else:
        return False


_all_classes: dict[int, Collection] = {}


@overload
def class_(n: Literal[0]) -> type[Set]: ...
@overload
def class_(n: Literal[1]) -> Collection[Class[Literal[1]]]: ...
@overload
def class_(n: Literal[2]) -> Collection[Class[Literal[2]]]: ...
@overload
def class_(n: Literal[3]) -> Collection[Class[Literal[3]]]: ...
@overload
def class_(n: Literal[4]) -> Collection[Class[Literal[4]]]: ...
@overload
def class_(n: Literal[5]) -> Collection[Class[Literal[5]]]: ...
@overload
def class_(n: Literal[6]) -> Collection[Class[Literal[6]]]: ...
@overload
def class_(n: Literal[7]) -> Collection[Class[Literal[7]]]: ...
@overload
def class_(n: Literal[8]) -> Collection[Class[Literal[8]]]: ...
@overload
def class_(n: Literal[9]) -> Collection[Class[Literal[9]]]: ...
@overload
def class_(n: Literal[10]) -> Collection[Class[Literal[10]]]: ...
@overload
def class_(n: int) -> Collection[Class[int]]: ...
def class_(n: int) -> Collection[Class[int]]:
    """
    Create the python class `Collection{n}` whose instances are collections
    that can contain only all collections of type `Collection{n-1}`.
    Collection0 is the same as Set.
    So, Collection1() can use restricted comprehension over all Set instances,
    Collection2() can use restricted comprehension over Collection1 instances, etc.

    Note that a Collection{n} instance cannot contain a Collection{n-2} or lower instance.
    """
    if n == 0:
        from pylogic.structures.set_ import Set

        return Set
    elif n in _all_classes:
        return _all_classes[n]
    c = Collection(
        f"Collection{n}",
        (),
        {
            "__init__": class_n_init,
            "__repr__": class_n_repr,
            "__hash__": class_n_hash,
            "level": n,
            "contains": contains,
            "equals": equals,
            "containment_function": containment_function,
            "predicate": predicate,
            "copy": copy,
            "deepcopy": deepcopy,
            "illegal_occur_check": illegal_occur_check,
            "illegal_occur_check_pred": illegal_occur_check_pred,
        },
    )
    _all_classes[n] = c
    return c


# from pylogic.proposition.not_ import Not
# The class of all sets
Sets = class_(1)(name="Sets", containment_function=lambda x: isinstance(x, Set))


# The class of all sets that do not contain themselves
# SetsThatDontContainThemselves = class_(1)(
#     name="SetsThatDontContainThemselves",
#     predicate=lambda x: Sets.contains(x).and_(Not(x.contains(x))),
# )
