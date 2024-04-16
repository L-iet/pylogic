import sympy as sp
from pylogic.set.sets import Set
from pylogic.theorems.divisible import divisible

# print(dir(sp.S))
# ['Catalan', 'ComplexInfinity', 'Complexes', 'EmptySequence', 'EmptySet',
# 'EulerGamma', 'Exp1', 'GoldenRatio', 'Half', 'IdentityFunction', 'ImaginaryUnit',
# 'Infinity', 'Integers', 'NaN', 'Naturals', 'Naturals0', 'NegativeInfinity',
# 'NegativeOne', 'One', 'Pi', 'Rationals', 'Reals', 'TribonacciConstant',
# 'UniversalSet', 'Zero', '__call__', '__class__', '__delattr__', '__dir__',
# '__doc__', '__eq__', '__format__', '__ge__', '__getattr__', '__getattribute__',
# '__getstate__', '__gt__', '__hash__', '__init__', '__init_subclass__', '__le__',
# '__lt__', '__module__', '__ne__', '__new__', '__reduce__', '__reduce_ex__',
# __repr__', '__setattr__', '__sizeof__', '__slots__', '__str__',
# '__subclasshook__', '_classes_to_install', 'false', 'register', 'true']

x, y, z = sp.symbols("x y z", integer=True)
w = x / y

# A = Set(name="A", containment_function=lambda t: t == x)
# print(A.contains(x).by_containment_func().is_proven)

A = sp.Set("A")


print(divisible(x, 2))
