from pylogic.constant import Constant

x = Constant("x", integer=True, positive=True)
y = Constant("y", integer=True, positive=True)
z = Constant("z", integer=True, positive=True)
print((x + y).is_positive)
print(x.is_zero, x._is_zero)
