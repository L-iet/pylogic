from __future__ import annotations
from abc import ABC, abstractmethod
from collections.abc import Iterable
from typing import (
    Any,
    Literal,
    Self,
    Callable,
    TYPE_CHECKING,
    Sequence,
    TypeIs,
    cast,
    TypeVar,
    overload,
    NewType,
)
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

if TYPE_CHECKING:
    from pylogic.typing.collection import ReadOnlyList, MutableOnlyList


class _Path(list[int]):
    """
    A class representing a path in a tree structure, where each element is an index
    of a child in the parent's children list.

    An empty path `[]` represents the root object, while a path `[0]`
    represents the first child of the root object.
    """

    def __init__(self, *args: Any, **kwargs: Any) -> None:
        super().__init__(*args, **kwargs)


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
    hash_attrs : tuple[str, ...]
        A tuple of attribute names that should be used to compute the hash of the
        object.
    """

    children: list[_PylogicObject]
    child_dependent_attrs: tuple[str, ...] = ("children", "leaves")
    child_independent_attrs: tuple[str, ...] = ()
    hash_attrs: tuple[str, ...] = ()
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
                        _PylogicObject._from_dict(child)  # type: ignore
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
        Self
            An instance of the class.
        """
        dct = json.loads(json_str)
        return cls.from_dict(dct)

    def __init__(
        self,
        *,
        children: Sequence[_PylogicObject] | None = None,
        reference_object: Self | None = None,
        **kwargs: Any,
    ) -> None:
        self.children = (
            children
            if isinstance(children, list)
            else list(children) if children is not None else []
        )
        self.update_child_dependent_attrs()
        if reference_object is None:
            self.init_child_independent_attrs(**kwargs)
        else:
            self.update_child_independent_attrs(reference_object)
        self.post_init()

    def __hash__(self) -> int:
        """
        Return a hash of the object based on its class and children.
        """
        hash_attrs = tuple(getattr(self, attr) for attr in self.hash_attrs)
        return hash((self.__class__.__qualname__, *hash_attrs, *self.children))

    def eq_child_independent_attrs(self, other: _PylogicObject) -> bool:
        """
        Check if the child-independent attributes of this object and `other`
        are equal.

        Parameters
        ----------
        other : _PylogicObject
            The object to compare against.

        Returns
        -------
        bool
            `True` if the child-independent attributes are equal, `False` otherwise.
        """
        if self.child_independent_attrs != other.child_independent_attrs:
            return False
        for attr in self.child_independent_attrs:
            value = getattr(self, attr)
            other_value = getattr(other, attr)
            if value != other_value:
                return False
        return True

    def __eq__(self, other: object) -> bool:
        """
        Check if two objects are equal.

        To be equal, `other` must be an instance of the class of this object (not
        a subclass), their child-independent attributes must be equal and their
        children must be equal.
        """
        if not isinstance(other, _PylogicObject):
            return NotImplemented
        return (
            self.__class__ == other.__class__
            and self.eq_child_independent_attrs(other)
            and self.children == other.children
        )

    def __repr__(self) -> str:
        """
        Return a string representation of the object, including its class name,
        and child-independent attributes.
        """
        attrs = [
            f"{attr}={getattr(self, attr)!r}" for attr in self.child_independent_attrs
        ]
        if len(self.children) == 0:
            attrs.append("children=[]")
        else:
            attrs.append("children=[...]")  # Avoid printing all children in repr
        attrs = ", ".join(attrs)
        return f"{self.__class__.__qualname__}({attrs})"

    def equal_up_to_subclass(self, other: _PylogicObject) -> bool:
        """
        Check if two objects are essentially equal, but may be of different classes.

        To compare equal, the following conditions must be met:
        - `other` is an instance of this class, or this object is an instance
        of `other.__class__`
        - their child-independent attributes must be equal
        - their children must be equal, up to subclasses.

        Parameters
        ----------
        other : _PylogicObject
            The object to compare against.

        Returns
        -------
        bool
            `True` if the objects are equal up to subclass, `False` otherwise.
        """

        return (
            (isinstance(other, self.__class__) or isinstance(self, other.__class__))
            and self.eq_child_independent_attrs(other)
            and len(self.children) == len(other.children)
            and all(
                selfchild.equal_up_to_subclass(otherchild)
                for selfchild, otherchild in zip(self.children, other.children)
            )
        )

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
        """
        return self.__copy__()

    def deepcopy(self) -> Self:
        """
        Create a deep copy of the object.
        """
        return self.__deepcopy__()

    @abstractmethod
    def update_child_dependent_attrs(self) -> None:
        """
        Update the attributes that depend on the children of the object.
        This method should be implemented by subclasses.
        This is called during initialization after `children` has been set.

        This method should not take any arguments. If a subclass does not have more
        child-dependent attributes, just call `super().update_child_dependent_attrs()`.
        """
        self.leaves: list[_PylogicObject] = []
        for child in self.children:
            if len(child.children) == 0:
                self.leaves.append(child)
            else:
                self.leaves.extend(child.leaves)

    @abstractmethod
    def init_child_independent_attrs(self, **kwargs: Any) -> None:
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

    def post_init(self) -> None:
        """
        This method should be implemented by subclasses if custom logic is needed
        after initialization, such as validation.

        It is called after all attributes have been set, with no arguments.
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
        dct: dict[str, Any] = {}
        for attr in self.__slots__:
            value = getattr(self, attr)
            if isinstance(value, _PylogicObject):
                dct[attr] = value.to_dict()
            elif isinstance(value, (list, tuple, set)):
                value: Iterable[Any]
                dct[attr] = [to_dict(child) for child in value]
            else:
                dct[attr] = to_dict(value)
        dct["class_module"] = self.__class__.__module__
        dct["class_name"] = self.__class__.__qualname__
        return dct

    def to_json(self, **kwargs: Any) -> str:
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
        **kwargs: Any,
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
            in the children list. An empty path `[]` represents the root object,
            while a path `[0]` represents the first child of the root object.

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

        # the index to look at in each path in positions
        _depth = cast(int, kwargs.get("_depth", 0))
        # the path we are currently going through
        # if None, this is the root object
        _path = cast(list[int] | None, kwargs.get("_path"))
        replace_all: bool = False
        if _path is None:
            assert _depth == 0, "Depth must be 0 if path is None."
        if _path is not None and _depth == len(_path):
            replace_all = True
        if _path is not None and _depth > len(_path):
            raise ValueError(
                "Depth must be at most the length of the path if path is provided."
            )

        replace_all = positions is None or replace_all

        # shallow copy the children to avoid modifying the original object
        # but enable equal_check to work with something like `x is y`
        new_children = copy.copy(self.children)
        if replace_all:
            # may or may not be a recursive call
            # we need to replace all occurrences of the keys in replace_dict
            for old in replace_dict:
                new = replace_dict[old]
                if equal_check(old, self):
                    return new
            for i, child in enumerate(new_children):
                new_child = child.replace(
                    replace_dict, positions, equal_check, _depth=_depth, _path=_path
                )
                new_children[i] = new_child
        elif _path is None:
            # this is the root object, not a recursive call
            if TYPE_CHECKING:
                assert positions is not None
            for pth in positions:
                if not pth:
                    for old in replace_dict:
                        new = replace_dict[old]
                        if equal_check(old, self):
                            return new
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
            # this is a recursive call
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

    def _final_possible_unif(
        self,
        other: _PylogicObject,
        key_check: Callable[[_PylogicObject], TypeIs[UniVar]],
        _unif_so_far: Unification,
    ) -> bool | None:
        """
        Return False if there is an inconsistency, True if there is a consistency
        and None if `self` is not a variable.
        """
        if not key_check(self):
            return None
        if (val_so_far := _unif_so_far.get(self)) is not None:
            if val_so_far != other:  # inconsistent unification
                return False
        if self == other:
            return True
        _unif_so_far[self] = other
        return True

    def _unify(
        self,
        other: _PylogicObject,
        key_check: Callable[[_PylogicObject], TypeIs[UniVar]] | None = None,
        equal_excluding_children: (
            Callable[[_PylogicObject, _PylogicObject], bool] | None
        ) = None,
        *,
        _unif_so_far: Unification,
    ) -> bool:
        """
        Return True if the objects can be unified, False if they cannot, and None if
        the unification is not yet determined.
        """

        # default to leaf nodes
        if key_check is None:
            key_check = lambda o: cast(TypeIs[UniVar], len(o.children) == 0)
        equal_excluding_children = equal_excluding_children or (
            lambda x, y: (
                x.__class__ == y.__class__ and x.eq_child_independent_attrs(y)
            )
        )
        if (
            res := self._final_possible_unif(other, key_check, _unif_so_far)
        ) is not None:
            return res

        if not equal_excluding_children(self, other):
            return False

        if len(self.children) == 0:
            if len(other.children) == 0:
                return True
            return False

        if len(self.children) != len(other.children):
            return False

        for selfchild, otherchild in zip(self.children, other.children):
            res = selfchild._unify(
                otherchild,
                key_check=key_check,
                equal_excluding_children=equal_excluding_children,
                _unif_so_far=_unif_so_far,
            )
            if res is False:
                return False
        return True

    def unify(
        self,
        other: _PylogicObject,
        key_check: Callable[[_PylogicObject], TypeIs[UniVar]] | None = None,  # type: ignore
        equal_excluding_children: (
            Callable[[_PylogicObject, _PylogicObject], bool] | None
        ) = None,  # type: ignore
    ) -> Unification | None:
        """
        Unify two objects.

        If the objects are equal, return `True`. Otherwise, return a mapping of
        what objects in this object should be replaced with what objects in the
        other object to make them equal, or `None` if they cannot be unified.

        Parameters
        ----------
        other : _PylogicObject
            The object to unify with.

        key_check : Callable[[_PylogicObject], bool] | None, optional
            A function that checks if a subobject in this one can be a key in the
            unification dictionary returned. That is, it checks for what objects
            can serve as the "variables" or "basic objects" in the unification
            process. These objects will unify with any others.

        equal_excluding_children : Callable[[_PylogicObject, _PylogicObject], bool] | None, optional
            A function that checks if two objects are equal, ignoring their children.
            If not provided, it defaults to checking if the classes are the same and
            their child-independent attributes are equal.

        Returns
        -------
        dict[_PylogicObject, _PylogicObject] | None
            A dictionary mapping objects in this object to objects in the other
            object that should replace them to make the objects equal.

            If the objects are already equal, a **truthy** empty dictionary is
            returned.

            If they cannot be unified, `None` is returned.
        """
        unif = Unification()
        if self._unify(
            other,
            key_check=key_check,
            equal_excluding_children=equal_excluding_children,
            _unif_so_far=unif,
        ):
            return unif
        return None

    def _final_possible_multi_unif(
        self,
        other: _PylogicObject,
        key_check: Callable[[_PylogicObject], TypeIs[UniVar]],
        key_for_list_check: Callable[[_PylogicObject | MultiVar], TypeIs[MultiVar]],
        _unif_so_far: MultiUnification,
    ) -> bool | None:
        self_is_key_for_list = key_for_list_check(self)
        self_is_key: TypeIs[UniVar] = False  # type: ignore
        if self_is_key_for_list or (self_is_key := key_check(self)):
            val_so_far = _unif_so_far.get(self)
            if val_so_far is not None:
                # inconsistent unification
                if self_is_key_for_list and val_so_far != [other]:
                    return False
                elif self_is_key and val_so_far != other:
                    return False
            if self == other:
                return True
        if not (self_is_key_for_list or self_is_key):
            return None
        if self_is_key_for_list:
            _unif_so_far[self] = [other]
        elif self_is_key:
            _unif_so_far[self] = other  # type: ignore
        return True

    def _multi_unify(
        self,
        other: _PylogicObject,
        key_check: Callable[[_PylogicObject], TypeIs[UniVar]] | None = None,  # type: ignore
        key_for_list_check: Callable[[_PylogicObject | MultiVar], TypeIs[MultiVar]] | None = None,  # type: ignore
        equal_excluding_children: (
            Callable[[_PylogicObject, _PylogicObject], bool] | None
        ) = None,
        *,
        _unif_so_far: MultiUnification,
    ) -> MultiUnification | Literal[False]:
        """
        Return a MultiUnification if the objects can be unified, False if they
        cannot.
        """
        # Unlike with _unify, _unif_so_far here is always a new dictionary rather
        # than a reference to a global existing one
        # this is because we are backtracking in this method
        # this is also why we are returning a MultiUnification

        key_check: Callable[[_PylogicObject], TypeIs[UniVar]] = key_check or (
            (lambda o: len(o.children) == 0)
        )  # type: ignore
        equal_excluding_children = equal_excluding_children or (
            lambda x, y: (
                x.__class__ == y.__class__ and x.eq_child_independent_attrs(y)
            )
        )
        key_for_list_check: Callable[[_PylogicObject | MultiVar], TypeIs[MultiVar]] = (
            key_for_list_check or (lambda _: False)  # type: ignore
        )
        if (
            res := self._final_possible_multi_unif(
                other, key_check, key_for_list_check, _unif_so_far=_unif_so_far
            )
        ) is not None:
            if res is False:
                return False
            return _unif_so_far

        if not equal_excluding_children(self, other):
            return False

        if len(self.children) == 0:
            if len(other.children) == 0:
                return _unif_so_far
            return False
        self_children = cast(list[MultiVar | NonMultiVar], self.children)
        possible_ways_to_match_children = matches_to_actual(
            string_match(self_children, other.children, key_for_list_check),
            other.children,
        )
        for way in possible_ways_to_match_children:
            marginal_unif = MultiUnification()
            for k in way:
                # case 1: a key that unifies with a list
                if key_for_list_check(k):
                    v = way[k]
                    # if its a singleton list with the key itself,
                    # we should ignore it
                    if not (len(v) == 1 and v[0] == k):
                        if _unif_so_far.get(k) is not None and _unif_so_far[k] != v:
                            break
                        marginal_unif[k] = v
                    continue

                # case 2: a key that unifies with a single object
                # or a non-key # selfchild = k
                res = k._multi_unify(
                    way[k],
                    key_check=key_check,
                    key_for_list_check=key_for_list_check,
                    equal_excluding_children=equal_excluding_children,
                    _unif_so_far=_unif_so_far | marginal_unif,
                )
                if res is False:
                    break  # inconsistent unification
                else:
                    marginal_unif.update(res)  # type: ignore
            else:
                # if we are here, it means that all children were unified
                # and there was no conflict
                # so we can add the multivars to the unification so far
                return _unif_so_far | marginal_unif

        return False

    def multi_unify(
        self,
        other: _PylogicObject,
        key_check: Callable[[_PylogicObject], TypeIs[UniVar]] | None = None,  # type: ignore
        key_for_list_check: Callable[[_PylogicObject | MultiVar], TypeIs[MultiVar]] | None = None,  # type: ignore
        equal_excluding_children: (
            Callable[[_PylogicObject, _PylogicObject], bool] | None
        ) = None,  # type: ignore
    ) -> MultiUnification | None:
        """
        Unify this object with another object. In the return value, one object
        can be unified with a list of objects.

        Parameters
        ----------
        other : _PylogicObject
            The object to unify with.

        key_check : Callable[[_PylogicObject], bool] | None, optional
            A function that checks if a subobject in this one can be a key in the
            unification dictionary returned. That is, it checks for what objects
            can serve as the "variables" or "basic objects" in the unification
            process. These objects will unify with any others.

        key_for_list_check : Callable[[_PylogicObject], bool] | None, optional
            A function that checks if a subobject in this one can be a key in the
            unification dictionary returned (a "multi-variable"). The value of
            this key will be a list of objects from `others` that unify with it.
            If not provided, it defaults to always returning `False`, so a regular
            unification will be performed.

        equal_excluding_children : Callable[[_PylogicObject, _PylogicObject], bool] | None, optional
            A function that checks if two objects are equal, ignoring their children.
            If not provided, it defaults to checking if the classes are the same and
            their child-independent attributes are equal.

        Returns
        -------
        dict[_PylogicObject, _PylogicObject | list[_PylogicObject]] | None
            A dictionary mapping objects in this object to objects (or lists of
            objects) in the `others`
            that should replace them to make the objects equal.

            This is just the first unification found. It may not be the only unification
            possible, but it is guaranteed to be a valid unification. By "first",
            we mean that the length of the value (a list) of the highest and leftmost
            multi-unifiable ("key-for-list") object is the smallest possible.

            If the objects are already equal, a **truthy** empty dictionary is
            returned.

            If they cannot be unified, `None` is returned.
        """
        if unif := self._multi_unify(
            other,
            key_check=key_check,
            key_for_list_check=key_for_list_check,
            equal_excluding_children=equal_excluding_children,
            _unif_so_far=MultiUnification(),
        ):
            return unif
        return None

    def _subobject_find(
        self,
        obj: _PylogicObject,
        path: list[int],
    ) -> Path | None:
        for i, child in enumerate(self.children):
            if child == obj:
                path.append(i)
                return path
            if (pth := child._subobject_find(obj, path + [i])) is not None:
                return pth
        return None

    def subobject_find(self, obj: _PylogicObject) -> Path | None:
        """
        Find the path to a subobject in the children of this object.

        A path can be empty, which means that the object is this one itself.

        If the object is not found, `None` is returned.

        Parameters
        ----------
        obj : _PylogicObject
            The object to find in the children.

        Returns
        -------
        list[int] | None
            The path to the subobject if found, or `None` if not found.
        """
        if self == obj:
            return []
        return self._subobject_find(obj, list[int]())

    def _subobject_find_all(
        self,
        obj: _PylogicObject,
        path: list[int],
        paths: MutableOnlyList[list[int]],
    ) -> None:
        for i, child in enumerate(self.children):
            if child == obj:
                paths.append(path + [i])
                continue
            child._subobject_find_all(obj, path + [i], paths)

    def subobject_find_all(self, obj: _PylogicObject) -> list[list[int]]:
        """
        Find all paths to a subobject in the children of this object.

        A path can be empty, which means that the object is this one itself.

        If the object is not found, an empty list is returned.

        Parameters
        ----------
        obj : _PylogicObject
            The object to find in the children.

        Returns
        -------
        list[list[int]]
            A list of paths to the subobject if found, or an empty list if not found.
        """
        if self == obj:
            return [[]]
        paths: list[list[int]] = []
        self._subobject_find_all(obj, [], paths)
        return paths


UniVar = NewType("UniVar", _PylogicObject)
MultiVar = NewType("MultiVar", _PylogicObject)
NonMultiVar = NewType("NonMultiVar", _PylogicObject)


class Unif[T, U, V, W](dict[T | U, V | W]):
    """
    A dictionary-like class for unification results, where keys are objects
    that should be replaced and values are the objects to replace them with.
    """

    def __init__(self, *args: Any, **kwargs: Any) -> None:
        super().__init__(*args, **kwargs)

    def __bool__(self) -> Literal[True]:
        """
        Always returns True, as an instance of Unification is always considered
        a valid unification result.
        """
        return True

    if TYPE_CHECKING:

        A = TypeVar("A")
        B = TypeVar("B")

        @overload
        def __getitem__(self, key: T) -> V: ...
        @overload
        def __getitem__(self, key: U) -> W: ...
        def __getitem__(self, key: T | U) -> V | W: ...

        @overload
        def __or__(self, value: Unif[T, U, V, W]) -> Unif[T, U, V, W]: ...
        @overload
        def __or__(self, value: dict[T | U, V | W]) -> dict[T | U, V | W]: ...
        @overload
        def __or__(self, value: dict[A, B]) -> dict[A | T | U, B | V | W]: ...
        def __or__(
            self, value: Unif[T, U, V, W] | dict[T | U, V | W] | dict[A, B]
        ) -> Unif[T, U, V, W] | dict[T | U, V | W] | dict[A | T | U, B | V | W]: ...


dict[str, int].__or__
Unification = Unif[UniVar, UniVar, _PylogicObject, _PylogicObject]
MultiUnification = Unif[UniVar, MultiVar, _PylogicObject, Sequence[_PylogicObject]]


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
        return [to_dict(item) for item in cast(Iterable[Any], value)]
    elif isinstance(value, dict):
        return {k: to_dict(v) for k, v in cast(dict[Any, Any], value).items()}
    return value


if TYPE_CHECKING:

    class MatchIndicesDict[A, B](dict[A | B, int | tuple[int, int]]):
        """
        A is a variable, B is a multi-variable (variable that unifies to a list
        of values).
        """

        @overload
        def __getitem__(self, key: A) -> int: ...
        @overload
        def __getitem__(self, key: B) -> tuple[int, int]: ...
        def __getitem__(self, key: A | B) -> int | tuple[int, int]: ...

        def __or__(self, value: MatchIndicesDict[A, B]) -> MatchIndicesDict[A, B]: ...

    class MatchDict[M1, M2, M3, M4](dict[M1 | M2, M3 | M4]):
        """
        M1 maps to M3, M2 maps to M4.

        Start from more specific types (subtypes) to more general types.
        """

        @overload
        def __getitem__(self, key: M1) -> M3: ...
        @overload
        def __getitem__(self, key: M2) -> M4: ...
        def __getitem__(self, key: M1 | M2) -> M3 | M4: ...

        def __or__(
            self, value: MatchDict[M1, M2, M3, M4]
        ) -> MatchDict[M1, M2, M3, M4]: ...


def string_match[A, B](
    pattern: Sequence[A | B],
    target: Sequence[Any],
    is_multi_var: Callable[[A | B], TypeIs[A]],
    *,
    _patternstart: int = 0,
    _targetstart: int = 0,
) -> list[MatchIndicesDict[A, B]]:
    """
    This function attempts to match a pattern against a target sequence.
    The pattern consists of variables and multi-variables, where:
    - A variable matches a single element in the target sequence.
    - A multi-variable matches a sequence of elements in the target sequence,
        which can be empty.
    The function returns a list of dictionaries, where each dictionary represents
    a possible match. The keys in the dictionary are the variables and multi-variables
    from the pattern, and the values are either indices in the target sequence
    (for variables) or tuples of indices (for multi-variables).

    Parameters
    ----------
    pattern : Sequence[A | B]
        The pattern to match against the target sequence.
        It can contain variables (A) and multi-variables (B).
    target : Sequence[Any]
        The target sequence to match the pattern against.
    is_multi_var : Callable[[A | B], bool]
        A function that checks if a given element is a multi-variable.

    Returns
    -------
    list[dict[A | B, int | tuple[int, int]]]
        A list of dictionaries representing the matches found.
        Each dictionary maps variables and multi-variables from the pattern
        to their corresponding indices or slices in the target sequence.
    """
    # given a pattern string and another string, this is an algorithm
    # to match them up (unify them). Return all possible matches,
    # or an empty collection.

    # each match is a dict of multiVar -> range indicies in target
    # and var -> index

    # The pattern string is made of two types of symbols: variables
    # and multiVariables. Examples of variables: w,x,y,z.
    # Examples of multiVars: *x, *y, etc.
    # A var matches to any character.
    # A multiVar matches to a list of characters, which can be empty.
    # A string is a comma-separated sequence (i guess a python list)
    # in this case.
    # Example: inputs *a,y,*b,z and 1,2,3,4
    # outputs:
    # {a: [], y: 1, b: [2,3], z: 4},
    # {a: [1], y: 2, b: [3], z: 4},
    # {a: [1,2], y: 3, b: [], z: 4}

    # both empty
    if len(pattern) == _patternstart and len(target) == _targetstart:
        return [{}]  # the do-nothing match # type: ignore

    # pattern empty
    if len(pattern) == _patternstart:
        return []  # no match

    if is_multi_var(pattern[_patternstart]):
        results: list[MatchIndicesDict[A, B]] = []
        for i in range(_targetstart, len(target) + 1):
            result = cast("MatchIndicesDict[A, B]", {})
            result[pattern[_patternstart]] = (_targetstart, i)
            remaining = string_match(
                pattern,
                target,
                is_multi_var=is_multi_var,
                _patternstart=_patternstart + 1,
                _targetstart=i,
            )
            if not remaining:
                continue
            results.extend([result | r for r in remaining])
        return results

    else:
        result = cast("MatchIndicesDict[A, B]", {})
        result[pattern[_patternstart]] = _targetstart
        remaining = string_match(
            pattern,
            target,
            _patternstart=_patternstart + 1,
            _targetstart=_targetstart + 1,
            is_multi_var=is_multi_var,
        )
        if not remaining:
            return []
        else:
            return [result | r for r in remaining]


def matches_to_actual[M1, M2, M3](
    matches: ReadOnlyList[MatchIndicesDict[M1, M2]], target: Sequence[M3]
) -> list[MatchDict[M1, M2, Sequence[M3], M3]]:
    """
    Given a list of matches (dictionaries mapping variables and multi-variables
    to indices or slices in the target sequence), convert them to a list of
    dictionaries mapping variables and multi-variables to actual values in the
    target sequence.

    Parameters
    ----------
    matches : list[dict[M1 | M2, tuple[int, int] | int]]
        A list of dictionaries representing the matches found by `string_match`.
        Each dictionary maps variables and multi-variables to indices or slices
        in the target sequence.
    target : Sequence[M3]
        The target sequence from which the values are extracted.

    Returns
    -------
    list[dict[M1 | M2, Sequence[M3] | M3]]
        A list of dictionaries where each dictionary maps variables and multi-variables
        to their corresponding values in the target sequence.
        For variables, the value is a single element from the target sequence.
        For multi-variables, the value is a list of elements from the target sequence.
    """

    def _match(m: MatchIndicesDict[M1, M2]) -> MatchDict[M1, M2, Sequence[M3], M3]:
        d = cast("MatchDict[M1, M2, Sequence[M3], M3]", {})
        for k, v in m.items():
            if isinstance(v, int):
                d[k] = target[v]
            else:
                d[k] = target[slice(*v)]
        return d

    return list(map(_match, matches))
