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


class _Path(list[int]):
    """
    A class representing a path in a tree structure, where each element is an index
    of a child in the parent's children list.

    This class is used to represent the path to a specific object in a tree structure,
    allowing for easy traversal and manipulation of the tree.
    """

    def __init__(self, *args, **kwargs) -> None:
        super().__init__(*args, **kwargs)
        if not all(isinstance(i, int) for i in self):
            raise TypeError("All elements of Path must be integers.")


Path = _Path | list[int] | tuple[int, ...]


class _PylogicObject(ABC):
    """
    Base class for all Pylogic objects. The structure is essentially a tree.

    Parameters
    ----------
    children : list[_PylogicObject] | None, optional
        A list of child objects. If None, an empty list is used.
    reference_object : Self | None, optional
        A reference to the object itself, used to update independent attributes.
        This is useful when the object is being copied, and the independent attributes
        need to be updated based on the original object.
    kwargs : dict[str, Any], optional
        Additional keyword arguments that can be used to initialize independent attributes.

    Attributes
    ----------
    children : list[_PylogicObject]
        A list of child objects. `children` should not contain an object that has
        this object as a descendant to avoid infinite recursion with most of the
        methods, such as `__repr__`, `__eq__` etc.
    child_dependent_attrs : tuple[str, ...]
        A tuple of attribute names that depend on the children of the object.
        These attributes should be updated when `children` is set or modified.
    child_independent_attrs : tuple[str, ...]
        A tuple of attribute names that do not depend on the children of the object.
    """

    children: list[_PylogicObject]
    child_dependent_attrs: tuple[str, ...] = ("children", "leaves")
    child_independent_attrs: tuple[str, ...] = ()
    __slots__: tuple[str, ...] = child_dependent_attrs + child_independent_attrs

    @staticmethod
    def _from_dict(dct: dict[str, Any]) -> dict[str, Any] | _PylogicObject:
        if "class_name" not in dct or "class_module" not in dct:
            return dct
        # __import__ needs fromlist to actually import the module for some reason
        mod = __import__(dct["class_module"], fromlist=[dct["class_name"]])
        cls = getattr(mod, dct["class_name"])
        args = cls.dict_to_constructor_kwargs(dct)
        return cls(**args)

    @classmethod
    def dict_to_constructor_kwargs(cls, dct: dict[str, Any]) -> dict[str, Any]:
        """
        Convert a dictionary representation of the object to constructor arguments.
        The class it is called on should match the keys `class_module` and `class_name`
        in the dictionary.

        Subclasses can override this method to match different dictionary structures
        and convert them to the corresponding constructor arguments. But they
        must handle the case where the dictionary contains the key `"children"`.

        Parameters
        ----------
        dct : dict[str, Any]
            A dictionary representation of the object.

        Returns
        -------
        dict[str, Any]
            A dictionary with keys as constructor argument names and values as
            their values.
        """
        assert dct.get("class_module") == cls.__module__, (
            f"Module name mismatch: expected {cls.__module__}, "
            f"but got {dct.get('class_module')}"
        )
        assert dct.get("class_name") == cls.__qualname__, (
            f"Class name mismatch: expected {cls.__qualname__}, "
            f"but got {dct.get('class_name')}"
        )
        dct.pop("class_module", None)
        dct.pop("class_name", None)
        for key in dct:
            if isinstance(dct[key], dict):
                dct[key] = _PylogicObject._from_dict(dct[key])
            elif isinstance(dct[key], list):
                dct[key] = [
                    (
                        _PylogicObject._from_dict(child)
                        if isinstance(child, dict)
                        else child
                    )
                    for child in dct[key]
                ]
        return dct

    @classmethod
    def from_dict(cls, dct: dict[str, Any]) -> Self:
        """
        Create an instance of the class from a dictionary representation.

        Parameters
        ----------
        dct : dict[str, Any]
            A dictionary representation of the object.

        Returns
        -------
        Self
            An instance of the class.
        """
        kwargs = cls.dict_to_constructor_kwargs(dct)
        return cls(**kwargs)

    @classmethod
    def from_json(cls, json_str: str) -> Self:
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
        children: list[_PylogicObject] | None = None,
        reference_object: Self | None = None,
        **kwargs,
    ) -> None:
        self.children: list[_PylogicObject] = (
            children
            if isinstance(children, list)
            else list(children) if children is not None else []
        )
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

    def __copy__(self) -> Self:
        """
        Create a shallow copy of the object.
        """
        return self.__class__(children=self.children, reference_object=self)

    def __deepcopy__(self, memo: dict[int, _PylogicObject] | None = None) -> Self:
        """
        Create a deep copy of the object.

        In case the object is already in `children`, it will return the same object
        as the original object, to avoid infinite recursion.
        """
        if memo is None:
            memo = {}
        if id(self) in memo:
            return memo[id(self)]  # type: ignore
        new_object = self.__class__(
            children=copy.deepcopy(self.children, memo=memo), reference_object=self
        )
        memo[id(self)] = new_object
        return new_object

    def copy(self) -> Self:
        """
        Create a shallow copy of the object.
        This is an alias for `__copy__`.
        """
        return self.__copy__()

    def deepcopy(self) -> Self:
        """
        Create a deep copy of the object.
        This is an alias for `__deepcopy__`.
        """
        return self.__deepcopy__()

    @abstractmethod
    def update_child_dependent_attrs(self) -> None:
        """
        Update the attributes that depend on the children of the object.
        This method should be implemented by subclasses.
        This is called during initialization after `children` has been set.

        This method should not take any argumets. If a subclass does not have more
        child-dependent attributes, just call `super().update_child_dependent_attrs()`.
        """
        self.leaves: list[_PylogicObject] = []
        for child in self.children:
            if len(child.children) == 0:
                self.leaves.append(child)
            else:
                self.leaves.extend(child.leaves)

    @abstractmethod
    def init_child_independent_attrs(self, **kwargs) -> None:
        """
        Set the initial values for the independent attributes of the object.
        This method should be implemented by subclasses.
        It is called on initialization if the `reference_object` is `None` (object
        is not being copied).

        This method does not receive the children or `reference_object` as arguments,
        as it should not depend on them.
        It should receive other arguments from the `__init__` method needed to
        initialize the independent attributes. It should also handle unknown
        or unexpected keyword arguments appropriately.

        Parameters
        ----------
        kwargs : dict[str, Any]
            Additional keyword arguments that can be used to initialize independent
            attributes, passed from the `__init__` method.
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

        Parameters
        ----------
        reference_object : Self
            The object from which to copy the independent attributes.
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
            The dictionary will contain the class name (key `class_name`) and
            the module name (key `class_module`) of the class, as well as all
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
        dct["class_module"] = self.__class__.__module__
        dct["class_name"] = self.__class__.__qualname__
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
        positions: list[Path] | None = None,
        equal_check: Callable[[_PylogicObject, _PylogicObject], bool] | None = None,
        **kwargs,
    ) -> _PylogicObject:
        """
        Replace (substitute) the objects in the `children` list based on the provided
        `replace_dict` and `positions`.

        Objects at higher levels (closer to the root) will be replaced prior to
        objects at lower levels (closer to the leaves). So if `a` has children
        `[b, c]`, and `replace_dict` is `{a: d, b: e}`, then `a` will be replaced
        with `d` and `e` will not appear in the result (assuming it does not appear
        elsewhere in the tree).

        Parameters
        ----------
        replace_dict : dict[_PylogicObject, _PylogicObject]
            A dictionary where keys are objects to be replaced and values are the
            new objects to replace them with.
        positions : list[list[int]] | None, optional
            A list of paths to the positions where the replacements
            should occur.
            Each path is a list of indices representing the path to the object
            in the children list.

            For example, if the object has children `[a, b, c]`, `b` has children
            `[d, e]`, and `c` has children `[e]`, and you want to replace only the
            `e` in `c`, you would pass `positions=[[2, 0]]`, where `2` is the index
            of `c` in the children list, and `0` is the index of `e` in `c`'s children
            list.

            If `None`, all occurrences of the keys in `replace_dict` will be replaced
            in the object, regardless of their position.

            If an empty list is provided, no replacements will be made.
        equal_check : Callable[[_PylogicObject, _PylogicObject], bool] | None, optional
            A function that checks if the key in `replace_dict` is equal to the object.
            If not provided, it defaults to a simple equality check (`x == y`).
            If it is not a symmetric function, it could lead to unexpected behavior.

        Returns
        -------
        _PylogicObject
            A new object with the replacements made. The original object is not
            modified.
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
