# pyright: reportInvalidTypeForm=false
from __future__ import annotations

from typing import TYPE_CHECKING, Self, TypedDict, TypeVar

from pylogic.inference import Inference
from pylogic.proposition.proposition import Proposition

if TYPE_CHECKING:
    from pylogic.proposition.not_ import Not
    from pylogic.proposition.or_ import Or

TProposition = TypeVar("TProposition", bound="Proposition")
UProposition = TypeVar("UProposition", bound="Proposition")
InferenceRule = TypedDict("InferenceRule", {"name": str, "arguments": list[str]})


class Contradiction(Proposition):
    _inference_rules: list[InferenceRule] = [
        {"name": "thus_assumptions_cannot_all_hold", "arguments": []}
    ]
    """
    A contradiction can be assumed.
    """

    def __init__(self, **kwargs) -> None:
        super().__init__(
            "contradiction",
            description="contradiction",
            **kwargs,
        )
        self.is_atomic = True
        self._set_init_inferred_attrs()

    def __eq__(self, other: Contradiction) -> bool:
        if not isinstance(other, Contradiction):
            return NotImplemented
        return True

    def deepcopy(self) -> Self:
        return self.__class__()

    def copy(self) -> Self:
        return self.__class__()

    # def thus_assumptions_cannot_all_hold(
    #     self,
    # ) -> Or[Proposition, ...] | Not[Proposition]:
    #     """
    #     Logical inference rule. Given a contradiction, return the proposition
    #     that not all of the assumptions can hold at the same time.

    #     In classical logic, this is the same as the disjunction of the negations of the
    #     assumptions.

    #     In intuitionistic logic, this is the negation of the conjunction of the assumptions.
    #     """
    #     from pylogic.enviroment_settings.settings import settings
    #     from pylogic.proposition.and_ import And
    #     from pylogic.proposition.not_ import Not, neg
    #     from pylogic.proposition.or_ import Or

    #     assert self.is_proven, "This contradiction is not proven"
    #     if len(self.from_assumptions) == 1:
    #         return neg(
    #             self.from_assumptions.pop(),
    #             description="",
    #             _is_proven=True,
    #             _assumptions=self.from_assumptions,
    #             _inference=Inference(self, rule="thus_assumptions_cannot_all_hold"),
    #         )
    #     if settings["USE_CLASSICAL_LOGIC"]:
    #         return Or(
    #             *[neg(a) for a in self.from_assumptions],  # type: ignore
    #             description="",
    #             _is_proven=True,
    #             _assumptions=self.from_assumptions,
    #             _inference=Inference(self, rule="thus_assumptions_cannot_all_hold"),
    #         )
    #     return Not(
    #         And(*self.from_assumptions),  # type: ignore
    #         description="",
    #         _is_proven=True,
    #         _assumptions=self.from_assumptions,
    #         _inference=Inference(self, rule="thus_assumptions_cannot_all_hold"),
    #     )
