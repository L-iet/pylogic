from pylogic.constant import Constant
from pylogic.variable import Variable

a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z = [
    Variable(chr(i)) for i in range(97, 123)
]

(
    ca,
    cb,
    cc,
    cd,
    ce,
    cf,
    cg,
    ch,
    ci,
    cj,
    ck,
    cl,
    cm,
    cn,
    co,
    cp,
    cq,
    cr,
    cs,
    ct,
    cu,
    cv,
    cw,
    cx,
    cy,
    cz,
) = [Constant(chr(i)) for i in range(97, 123)]
