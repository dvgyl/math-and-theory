
if not __debug__:
    raise RuntimeError("Run this checker without Python optimization so that all mathematical checks execute.")

from fractions import Fraction as Q
from itertools import combinations, product
from math import prod
import json, platform

def symmetric_direction(x,v,M):
    """Differentiate each subset product before summation."""
    f,d1,d2 = Q(0),Q(0),Q(0)
    coefficients = [Q(1),M,Q(1),M,Q(1)]
    for size in range(5):
        for I in combinations(range(4), size):
            c = coefficients[size]
            f += c*prod(x[i] for i in I)
            for j in I:
                d1 += c*v[j]*prod(x[i] for i in I if i!=j)
                for k in I:
                    if k != j:
                        d2 += c*v[j]*v[k]*prod(x[i] for i in I if i not in (j,k))
    return f,d1,d2

def concavity():
    # The curvature difference has degree at most 2 in M and 6 in t.
    # This grid therefore proves equality of its rational coefficients.
    for M,t in product(map(Q,range(3)),map(Q,range(7))):
        f,d1,d2 = symmetric_direction([t]*4,[Q(1)]*4,M)
        assert 3*d1*d1-4*f*d2 == 48*(M*M-1)*(t*t-1)**2
    x = [Q(2),Q(2),Q(1,2),Q(1,2)]
    v = [Q(2),Q(2),Q(1),Q(1)]
    for M in map(Q,range(3)):
        f,d1,d2 = symmetric_direction(x,v,M)
        assert (f,d1,d2) == ((41+40*M)/4,27*(M+1),52+56*M)
        assert 4*f*d2-3*d1*d1 == (M-1)*(53*M+55)
    minus = [a-b/4 for a,b in zip(x,v)]
    plus = [a+b/4 for a,b in zip(x,v)]
    fm = symmetric_direction(minus,v,Q(2))[0]
    fp = symmetric_direction(plus,v,Q(2))[0]
    fc = symmetric_direction(x,v,Q(2))[0]
    assert fm == Q(933,64) and fp == Q(3597,64) and fc == Q(121,4)
    assert Q(977,500)**4 < fm and Q(1369,500)**4 < fp
    assert fc < Q(4691,2000)**4
    assert (Q(977,500)+Q(1369,500))/2 > Q(4691,2000)
    return {'diagonal_identity_grid':21,'directional_identity_grid':3,
            'M2_f_d1_d2':list(map(str,symmetric_direction(x,v,Q(2)))),
            'midpoint_f':[str(fm),str(fc),str(fp)]}

print(json.dumps({"python":platform.python_version(),"checks":concavity(),"status":"PASS","limitation":"Finite checks do not prove universal statements."},indent=2))
