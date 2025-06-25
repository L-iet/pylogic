from pylogic import *
from pylogic.structures.set_ import AllSequences, AllFiniteSequences

x,y,n = variables("x", "y", "n")
c1, c2 = variables("c_1", "c_2", sequence=True, set=True)
def forall_finite_collections_of(a, pred):
    inner_left = ForallInSet(n, Naturals, c1[n].is_in(a))
    inner_right = pred(c1)
    inner = inner_left.implies(inner_right)
    return ForallInSet(c1, AllFiniteSequences, inner)

def forall_collections_of(a, pred):
    return ForallInSet(c1, AllSequences, (ForallInSet(n, Naturals, c1[n].is_in(a))).implies(pred(c1)))


X = Set("X")
T = Set("T")

def is_topology(T, X):
    intersec = lambda c: GLB(c, X)
    p1 = T.is_subset_of(PowerSet(X))
    p2 = X.is_in(T)
    p3 = EmptySet.is_in(T)
    p4 = forall_finite_collections_of(T, lambda c: intersec(c).is_in(T))
    p5 = forall_collections_of(T, lambda c: Union(c).is_in(T))
    res = p1.and_(p2, p3, p4, p5)
    res.set_description(f"{T} is a top. on {X}")
    return res

def open_(x, T):
    return x.is_in(T)

def d(p):
    print(p.describe())


# powerset is a topology
pset = PowerSet(X)
to_prove = is_topology(pset, X)

p1 = pset.is_subset_of(pset).by_inspection()
d(p1)
p2 = X.is_in(pset).by_predicate(X.is_subset_of(X).by_inspection())
d(p2)
p3 = EmptySet.is_in(pset).by_predicate(
    EmptySet.is_subset_of(X).by_empty()
)
d(p3)
# p4
with AssumptionsContext() as ctx:
    c = ctx.var("c_1", sequence=True, finite=True, set=True)
    Ic = Intersection(c)
    hyp = ForallInSet(n, Naturals, c[n].is_in(pset)).assume()
    
    # prove Intersection(c) is subset of c0
    with AssumptionsContext() as ctxb:
        x = ctxb.var("x")
        pa = x.is_in(Ic).assume()
        pa.thus_predicate()(0)
    pf = Ic.is_subset_of(c[0]).by_definition(ctxb.get_first_proven())
    
    pf = Ic.is_in(pset).by_predicate(
        pf.transitive(hyp(0).thus_predicate())
    )
p4 = ctx.get_first_proven()
# print(p4, to_prove.propositions[3]) # not the same, variable is sequence
# d(p4)


#p5
with AssumptionsContext() as ctx:
    c = ctx.var("c_1", sequence=True, set=True)
    Uc = Union(c)
    hyp = ForallInSet(n, Naturals, c[n].is_in(pset)).assume()

    # prove Union(c) is subset of X
    with AssumptionsContext() as ctxb:
        x = ctxb.var("x")
        pa = x.is_in(Uc).assume()
        indx, (_, x_in_set) = pa.thus_predicate()
        set_ = x_in_set.right
        x_in_X = (
            hyp(indx)
            .thus_predicate()
            .definition
            (x)
            (x_in_set)
        )
    Uc.is_subset_of(X).by_definition(
        ctxb.get_first_proven()
    )
p5 = ctx.get_first_proven()
d(p5)

    
    
