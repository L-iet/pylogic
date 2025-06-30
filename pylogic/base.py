from __future__ import annotations
from abc import ABC, abstractmethod
from typing import Any, Self, Callable, Iterable, TYPE_CHECKING, cast
import copy
import json

"""
Methods:
- replace
- __hash__
- __eq__
- has_as_subtree
- find_subtree
- find_all_subtree
- unify
- eval_same
- copy
- deepcopy
- __new_init__
- __copy_init__

Attrs:
- children

Each class will define lists of child-dependent attributes,
and independent attributes.

For instance, Expr.symbols is a child-dependent attribute because it depends on
the symbols of its children.
Similarly, Expr.is_real is a child-dependent attribute because it depends on
the realness of its children (but the realness of the children does not depend
on it).

Proposition.is_proven is an independent attribute because it does not depend on
the children, but it is still an attribute of the object.

"""


class _PylogicObject(ABC):
    """
    Base class for all Pylogic objects.

    reference_object: Optional reference object to update independent attributes.
    This is used to update attributes that do not depend on the children of the object.
    """

    children: list[_PylogicObject]
    child_dependent_attrs: tuple[str, ...] = ("children",)
    child_independent_attrs: tuple[str, ...] = ()
    __slots__: tuple[str, ...] = child_dependent_attrs + child_independent_attrs

    @classmethod
    def dict_to_constructor_args(cls, dct: dict[str, Any]) -> dict[str, Any]:
        """
        Convert a dictionary representation of the object to constructor arguments.

        Parameters
        ----------
        dct : dict[str, Any]
            A dictionary representation of the object.

        Returns
        -------
        dict[str, Any]
            A dictionary with keys as constructor argument names and values as their values.
        """
        return dct

    @classmethod
    def from_dict(cls, dct: dict[str, Any]) -> _PylogicObject:
        """
        Create an instance of the class from a dictionary representation.

        Parameters
        ----------
        dct : dict[str, Any]
            A dictionary representation of the object.

        Returns
        -------
        _PylogicObject
            An instance of the class.
        """
        args = cls.dict_to_constructor_args(dct)
        return cls(**args)

    @classmethod
    def from_json(cls, json_str: str) -> _PylogicObject:
        """
        Create an instance of the class from a JSON string representation.

        Parameters
        ----------
        json_str : str
            A JSON string representation of the object.

        Returns
        -------
        _PylogicObject
            An instance of the class.
        """
        dct = json.loads(json_str)
        return cls.from_dict(dct)

    def __init__(
        self,
        *,
        children: Iterable[_PylogicObject] | None = None,
        reference_object: Self | None = None,
        **kwargs,
    ) -> None:
        self.children: list[_PylogicObject] = list(children) if children else []
        self.update_child_dependent_attrs()
        if reference_object is None:
            self.init_child_independent_attrs(**kwargs)
        else:
            self.update_child_independent_attrs(reference_object)
        self.validate_attrs()

    def __hash__(self) -> int:
        """
        Return a hash of the object based on its class and children.
        """
        return hash((self.__class__.__name__, *self.children))

    def __eq__(self, other: object) -> bool:
        """
        Check if two objects are equal based on their class and children.
        """
        if not isinstance(other, _PylogicObject):
            return NotImplemented
        return isinstance(other, self.__class__) and self.children == other.children

    def __copy__(self) -> _PylogicObject:
        """
        Create a shallow copy of the object.
        """
        return self.__class__(children=self.children, reference_object=self)

    def __deepcopy__(
        self, memo: dict[int, _PylogicObject] | None = None
    ) -> _PylogicObject:
        """
        Create a deep copy of the object.
        """
        if memo is None:
            memo = {}
        if id(self) in memo:
            return memo[id(self)]
        new_object = self.__class__(
            children=copy.deepcopy(self.children, memo=memo), reference_object=self
        )
        memo[id(self)] = new_object
        return new_object

    @abstractmethod
    def update_child_dependent_attrs(self) -> None:
        """
        Update the attributes that depend on the children of the object.
        This method should be implemented by subclasses.
        This is called during initialization after `children` has been set.
        """
        pass

    @abstractmethod
    def init_child_independent_attrs(self, **kwargs) -> None:
        """
        Set the initial values for the independent attributes of the object.
        This method should be implemented by subclasses.
        It is called on initialization if the `reference_object` is `None` (object
        is not being copied).

        This method does not receive the children or `reference_object` as arguments,
        as it should not depend on them.
        It should receive other arguments in the `__init__` method needed to
        initialize the independent attributes.
        """
        pass

    @abstractmethod
    def update_child_independent_attrs(self, reference_object: Self) -> None:
        """
        Update the attributes that do not depend on the children of the object,
        based on a reference object.
        This method should be implemented by subclasses.
        This is called during copying, where `reference_object` received in
        the initializer is not `None`.
        """
        pass

    def validate_attrs(self) -> None:
        """
        Validate the attributes of the object.
        This method should be implemented by subclasses if attribute validation
        is needed after initialization.
        """
        pass

    def to_dict(self) -> dict[str, Any]:
        """
        Convert the object to a dictionary representation.

        Returns
        -------
        dict[str, Any]
            A dictionary representation of the object.
        """
        dct = {}
        for attr in self.__slots__:
            value = getattr(self, attr)
            if isinstance(value, _PylogicObject):
                dct[attr] = value.to_dict()
            elif isinstance(value, (list, tuple, set)):
                dct[attr] = [to_dict(child) for child in value]
            else:
                dct[attr] = to_dict(value)
        return dct

    def to_json(self, **kwargs) -> str:
        """
        Convert the object to a JSON string representation.

        Returns
        -------
        str
            A JSON string representation of the object.
        """
        kwargs.pop("default", None)
        dct = self.to_dict()
        return json.dumps(dct, default=to_dict, **kwargs)

    def replace(
        self,
        replace_dict: dict[_PylogicObject, _PylogicObject],
        positions: list[list[int]] | None = None,
        equal_check: Callable[[_PylogicObject, _PylogicObject], bool] | None = None,
        **kwargs,
    ) -> _PylogicObject:
        """
        Replace the attributes of the object with the given values.

        equal_check checks if the key in `replace_dict` is equal to the object.
        If it is not a symmetric function, it could lead to unexpected behavior.
        """
        equal_check = equal_check or (lambda x, y: x == y)
        for old in replace_dict:
            new = replace_dict[old]
            if equal_check(old, self):
                return new

        # the index to look at in each path in positions
        _depth: int = kwargs.get("_depth", 0)
        # the path we are currently going through
        # if None, this is the root object
        _path: list[int] | None = kwargs.get("_path")
        replace_all: bool = False
        if _path is None:
            assert _depth == 0, "Depth must be 0 if path is None."
        if _path is not None and _depth == len(_path):
            replace_all = True
        if _path is not None and _depth > len(_path):
            raise ValueError(
                "Depth must be at most the length of the path if path is provided."
            )

        if TYPE_CHECKING:
            _depth = int(_depth)
            _path = cast(list[int] | None, _path)

        replace_all = positions is None or replace_all

        # shallow copy the children to avoid modifying the original object
        # but enable equal_check to work with something like `x is y`
        new_children = copy.copy(self.children)
        if replace_all:
            for i, child in enumerate(new_children):
                new_child = child.replace(
                    replace_dict, positions, equal_check, _depth=_depth, _path=_path
                )
                new_children[i] = new_child
        elif _path is None:
            if TYPE_CHECKING:
                assert positions is not None
            for pth in positions:
                if (
                    not pth
                    or (-len(new_children) > pth[0])
                    or (pth[0] >= len(new_children))
                ):
                    continue
                new_children[pth[0]] = new_children[pth[0]].replace(
                    replace_dict, positions, equal_check, _depth=1, _path=pth
                )
        else:
            if (
                not _path
                or (-len(new_children) > _path[_depth])
                or (_path[_depth] >= len(new_children))
            ):
                return self
            new_children[_path[_depth]] = new_children[_path[_depth]].replace(
                replace_dict, positions, equal_check, _depth=_depth + 1, _path=_path
            )

        new_object = self.__class__(children=new_children, reference_object=self)
        return new_object


def to_dict(value: Any) -> dict[str, Any] | list[Any] | Any:
    """
    Convert a value to a dictionary representation, if possible.
    If the value is a `_PylogicObject`, it will be converted to a dictionary using
    its `to_dict` method.
    If the value is a list, tuple, or set, it will be converted to a list of recursively
    converted values.
    If the value is a dictionary, it will be converted to a dictionary whose keys
    are the same, and values are recursively converted.
    Otherwise, it will be returned as is.

    Parameters
    ----------
    value : Any
        The value to convert.

    Returns
    -------
    Any
        The converted value.
    """
    if isinstance(value, _PylogicObject):
        return value.to_dict()
    elif isinstance(value, (list, tuple, set)):
        return [to_dict(item) for item in value]
    elif isinstance(value, dict):
        return {k: to_dict(v) for k, v in value.items()}
    return value
