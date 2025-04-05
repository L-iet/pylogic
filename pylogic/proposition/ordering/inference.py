from __future__ import annotations
from typing import Literal, TYPE_CHECKING

if TYPE_CHECKING:
    from pylogic.proposition.relation.binaryrelation import BinaryRelation

# TODO: Make this more generic to work with
# custom ordering classes
# and their reflexive closures
ConcType = Literal["<", "<=", ">", ">=", "=="]
def transitive(conclusion_type: ConcType, *props) -> BinaryRelation:
    """
    Logical inference rule.
    Prove a relation from a series of relations using transitivity.

    For example, if we have a series of relations:
    a = b, b <= c, c < d, d = e
    we can prove a < e (if conclusion type is <) or a <= e (if conclusion type is <=).
    """
    from pylogic.proposition.ordering.greaterthan import GreaterThan
    from pylogic.proposition.ordering.lessthan import LessThan
    from pylogic.proposition.ordering.lessorequal import LessOrEqual
    from pylogic.proposition.ordering.greaterorequal import GreaterOrEqual
    from pylogic.proposition.relation.equals import Equals
    from pylogic.helpers import  eval_same
    from pylogic.proposition.proposition import get_assumptions
    from pylogic.inference import Inference

    strict = False
    cls = None
    closure = None
    if conclusion_type == "<":
        strict = True
        cls = LessThan
        closure = LessOrEqual
    elif conclusion_type == "<=":
        cls = LessOrEqual
    elif conclusion_type == ">":
        strict = True
        cls = GreaterThan
        closure = GreaterOrEqual
    elif conclusion_type == ">=":
        cls = GreaterOrEqual
    elif conclusion_type == "==":
        cls = Equals
    else:
        raise ValueError(f"Invalid conclusion type: {conclusion_type}")
    
    prev_right = None
    any_strict = False
    for prop in props:
        assert prop.is_proven, f"{prop} is not proven"
        if prev_right is not None:
            assert eval_same(prop.left, prev_right), f"left side of {prop} does \
not match {prev_right} from previous relation"
        assert prop.__class__.is_transitive, f"{prop.__class__} is not transitive"
        assert prop.__class__ in [cls, closure, Equals], f"{prop} is not a {cls}{f' or {closure}' if closure else ''} or Equals"
        if strict and prop.__class__ == cls:
            any_strict = True
        prev_right = prop.right
    
    if strict and not any_strict:
        raise ValueError(f"At least one of the propositions must be strict ({cls})")
    
    new_p = cls(
        props[0].left,
        props[-1].right,
        _is_proven=True,
        _assumptions=set.union(
            *[get_assumptions(p) for p in props]
        ),
        _inference=Inference(*props, rule="transitive"),
    )
    return new_p
