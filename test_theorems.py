# from pylogic.theories.arithmetic import add_inv

# print(add_inv)

from pylogic import *
settings['PYTHON_OPS_RETURN_PROPS'] = True

x, y, z = constants('x', 'y', 'z', real=True)
h0, h1 = assume(x <= y, y <= z)
to_prove = x <= z

print(h0.transitive(h1))
print(has_been_proven(to_prove, h0.transitive(h1)))
