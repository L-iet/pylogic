# Lean example on triangle numbers https://ahelwer.ca/post/2020-04-05-lean-assignment/
from __future__ import annotations

import sys
from abc import ABC, abstractmethod
from typing import Self

# set the default warning filter to ignore internal warnings
# before importing any other modules
if not sys.warnoptions:
    import warnings

    from pylogic.warn import PylogicInternalWarning

    warnings.simplefilter("ignore", PylogicInternalWarning)


from pylogic.assumptions_context import (
    AssumptionsContext,
    conclude,
    context_variable,
    context_variables,
    ctx_var,
    ctx_vars,
)
from pylogic.constant import Constant, constants
from pylogic.enviroment_settings.set_universe import set_universe
from pylogic.enviroment_settings.settings import settings
from pylogic.expressions.abs import Abs
from pylogic.expressions.expr import Add, Expr, Mul, Pow, add, cbrt, mul, sqrt
from pylogic.expressions.function import CalledFunction, Function
from pylogic.expressions.gcd import Gcd
from pylogic.expressions.limit import Limit
from pylogic.expressions.min import MinElement
from pylogic.expressions.mod import Mod
from pylogic.expressions.piecewise import (
    OtherwiseBranch,
    Piecewise,
    PiecewiseBranch,
    PiecewiseExpr,
    otherwise,
)
from pylogic.expressions.prod import Prod
from pylogic.expressions.sequence_term import SequenceTerm
from pylogic.expressions.sum import Sum
from pylogic.helpers import Rational, assume, has_been_proven, is_prime, latex, todo
from pylogic.proposition.and_ import And
from pylogic.proposition.contradiction import Contradiction
from pylogic.proposition.exor import ExOr, Exor
from pylogic.proposition.iff import Iff
from pylogic.proposition.implies import Implies
from pylogic.proposition.not_ import Not, are_negs, neg
from pylogic.proposition.or_ import Or
from pylogic.proposition.ordering.greaterorequal import GreaterOrEqual
from pylogic.proposition.ordering.greaterthan import GreaterThan
from pylogic.proposition.ordering.lessorequal import LessOrEqual
from pylogic.proposition.ordering.lessthan import LessThan
from pylogic.proposition.ordering.partial import PartialOrder, StrictPartialOrder
from pylogic.proposition.ordering.total import StrictTotalOrder, TotalOrder
from pylogic.proposition.proposition import (
    Proposition,
    pred,
    predicate,
    predicates,
    preds,
    prop,
    proposition,
    propositions,
    props,
)
from pylogic.proposition.quantified.exists import (
    Exists,
    ExistsInSet,
    ExistsSubset,
    ExistsUnique,
    ExistsUniqueInSet,
    ExistsUniqueSubset,
)
from pylogic.proposition.quantified.forall import Forall, ForallInSet, ForallSubsets
from pylogic.proposition.relation.binaryrelation import BinaryRelation
from pylogic.proposition.relation.contains import IsContainedIn
from pylogic.proposition.relation.divides import Divides
from pylogic.proposition.relation.equals import Equals
from pylogic.proposition.relation.relation import Relation
from pylogic.proposition.relation.subsets import IsSubsetOf
from pylogic.structures.class_ import Class, class_
from pylogic.structures.grouplike.group import AbelianGroup, Group
from pylogic.structures.grouplike.loop import Loop
from pylogic.structures.grouplike.magma import Magma
from pylogic.structures.grouplike.monoid import Monoid
from pylogic.structures.grouplike.quasigroup import Quasigroup
from pylogic.structures.grouplike.semigroup import Semigroup
from pylogic.structures.ordered_set import OrderedSet
from pylogic.structures.ringlike.commutative_ring import CommutativeRIng
from pylogic.structures.ringlike.crooked_semiring import CrookedSemirIng
from pylogic.structures.ringlike.crooked_semirng import CrookedSemirng
from pylogic.structures.ringlike.division_ring import DivisionRIng
from pylogic.structures.ringlike.field import Field
from pylogic.structures.ringlike.nearring import NearrIng
from pylogic.structures.ringlike.ring import RIng
from pylogic.structures.ringlike.ringoid import Ringoid, RIngoid
from pylogic.structures.ringlike.rng import Rng
from pylogic.structures.ringlike.semiring import SemirIng
from pylogic.structures.ringlike.semirng import Semirng
from pylogic.structures.sequence import (
    FiniteSequence,
    Pair,
    PeriodicSequence,
    Sequence,
    Triple,
    sequences,
)
from pylogic.structures.set_ import (
    CartesPower,
    CartesProduct,
    Complement,
    Difference,
    EmptySet,
    FiniteCartesProduct,
    FiniteIntersection,
    FiniteSet,
    FiniteUnion,
    Intersection,
    SeqSet,
    Set,
    SingletonEmpty,
    Union,
    UniversalSet,
    sets,
)
from pylogic.syntax_helpers.if_ import If, if_
from pylogic.theories.natural_numbers import Prime
from pylogic.theories.numbers import Integers, Naturals, Rationals, Reals, one, zero
from pylogic.theories.real_numbers import Interval, interval
from pylogic.variable import Variable, unbind, variables


class _PylogicObject(ABC):
    """
    Base class for all pylogic objects.
    """

    @abstractmethod
    def replace(self, **kwargs) -> Self:
        """
        Replace the attributes of the object with the given values.
        """
        ...
