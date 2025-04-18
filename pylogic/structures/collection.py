from typing import TYPE_CHECKING, Generic, Self, TypeVar

# Hack for Type Checking
if TYPE_CHECKING:
    pass

    from pylogic.proposition.relation.equals import Equals
    from pylogic.structures.set_ import Set
    from pylogic.typing import Term

    T = TypeVar("T", bound=int, covariant=True)
    U = TypeVar("U", bound=Term)

    class Class(Set, Generic[T]):
        def equals(self, other: U, **kwargs) -> Equals[Self, U]: ...

    N = TypeVar("N", bound=Class, covariant=True)
else:
    N = TypeVar("N")


class Collection(type, Generic[N]):
    """
    Python metaclass for all collections/classes Set, Class{n}.
    """

    def __new__(cls, name, bases, dct):
        if name == "Class0":
            from pylogic.structures.set_ import Set

            return Set
        coll = super().__new__(cls, name, bases, dct)
        return coll

    def __eq__(self, other: object) -> bool:
        if isinstance(other, Collection):
            return self.__name__ == other.__name__ or (
                {self.__name__, other.__name__} == {"Set", "Class0"}
            )
        return NotImplemented

    def __hash__(self) -> int:
        return hash(self.__name__)

    def __repr__(self) -> str:
        return self.__name__

    if TYPE_CHECKING:

        def __call__(cls, *args, **kwargs) -> N:
            return super().__call__(*args, **kwargs)
