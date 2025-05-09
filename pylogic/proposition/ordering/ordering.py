from __future__ import annotations

from typing import TYPE_CHECKING, Protocol, Self

from pylogic.typing import PythonNumeric, Term

if TYPE_CHECKING:
    pass

    from pylogic.proposition.ordering.greaterthan import GreaterThan
    from pylogic.proposition.ordering.lessthan import LessThan


class _Ordering(Protocol):
    @classmethod
    def _multiply_by(
        cls,
        instance: GreaterThan | LessThan,
        x: Term,
        p: GreaterThan | LessThan,
        _sign: str = "positive",
        **kwargs,
    ) -> Self:
        from pylogic.proposition.ordering.greaterthan import GreaterThan
        from pylogic.proposition.ordering.lessthan import LessThan

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
            new_p = cls(x * instance.left, x * instance.right, **kwargs)  # type: ignore
        elif _sign == "negative":
            new_p = cls(x * instance.right, x * instance.left, **kwargs)  # type: ignore
        else:
            raise ValueError(f"Invalid sign: {_sign}")
        return new_p

    @classmethod
    def _mul(cls, instance: GreaterThan | LessThan, other: PythonNumeric) -> Self:
        from pylogic.inference import Inference
        from pylogic.proposition.ordering.greaterthan import GreaterThan
        from pylogic.proposition.ordering.lessthan import LessThan
        from pylogic.proposition.proposition import get_assumptions

        if isinstance(other, int) or isinstance(other, float):
            sign = "positive" if other > 0 else "negative"
            proof = (
                GreaterThan(other, 0, _is_proven=True)
                if sign == "positive"
                else LessThan(other, 0, _is_proven=True)
            )
            return cls._multiply_by(
                instance,
                other,
                proof,
                _sign=sign,
                _is_proven=instance.is_proven,
                _assumptions=get_assumptions(instance),
                _inference=Inference(instance, proof, rule="multiply_by_number"),
            )
        else:
            raise TypeError(
                f"Cannot multiply {instance} by {other}, use multiply_by_positive or multiply_by_negative"
            )

    def __add__(self, other: _Ordering) -> Self:
        cls = type(self)
        from pylogic.inference import Inference

        if not isinstance(other, cls):
            raise TypeError(f"Cannot add {self} to {other}")
        if self.is_proven and other.is_proven:
            from pylogic.proposition.proposition import get_assumptions

            inf = Inference(self, other, rule="add_inequalities")
            return cls(
                self.left + other.left,
                self.right + other.right,
                _is_proven=True,
                _assumptions=get_assumptions(self).union(get_assumptions(other)),
                _inference=inf,
            )
        else:
            return cls(
                self.left + other.left,
                self.right + other.right,
            )

    def __rtruediv__(self, other: Term) -> Self:
        """
        Currently, only used to invert an inequality.
        """
        from pylogic.helpers import python_to_pylogic
        from pylogic.proposition.proposition import get_assumptions
        from pylogic.inference import Inference

        other = python_to_pylogic(other)
        if other == 1:
            return self.__class__(
                1 / self.right,
                1 / self.left,
                _is_proven=self.is_proven,
                _assumptions=get_assumptions(self),
                _inference=(
                    Inference(self, rule="invert_inequality")
                    if self.is_proven
                    else None
                ),
            )
        raise ValueError(f"Cannot invert {self} with {other}. Only 1 is supported.")

    # TODO: implement __mul__
