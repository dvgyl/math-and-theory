
if not __debug__:
    raise RuntimeError("Run this checker without Python optimization so that all mathematical checks execute.")

from fractions import Fraction as Q
from itertools import combinations, product
from math import prod
import json, platform

def log_interval(x, terms=60):
    """Enclose log(x) by the atanh series and a geometric tail bound."""
    if x < 1:
        a, b = log_interval(1 / x, terms)
        return -b, -a
    z = (x - 1) / (x + 1)
    lower = 2 * sum((z ** (2*j+1) / (2*j+1) for j in range(terms)), Q(0))
    error = 2 * z ** (2*terms+1) / ((2*terms+1)*(1-z*z))
    return lower, lower + error

def best_of_two():
    p = [Q(2,5),Q(1,5),Q(1,5),Q(1,5)]
    q = [Q(0) for _ in p]
    for a,b in product(range(4), repeat=2):
        q[max(a,b)] += p[a]*p[b]
    win = sum((q[a]*p[b]*(int(a>b)+Q(int(a==b),2))
               for a,b in product(range(4), repeat=2)), Q(0))
    assert q == [Q(4,25),Q(5,25),Q(7,25),Q(9,25)]
    assert win == Q(163,250)
    lower, upper = log_interval(win/(1-win))
    lower += 1/win-2
    upper += 1/win-2
    for pi,qi in zip(p,q):
        lo,hi = log_interval(qi/pi)
        lower -= qi*hi
        upper -= qi*lo
    assert lower > Q(1,500)
    assert Q(2375504921683,10**15) < lower < upper < Q(2375504921686,10**15)
    return {'q':list(map(str,q)), 'W':str(win), 'gap_lower':str(lower),
            'gap_upper':str(upper), 'gap_approx':float((lower+upper)/2)}

print(json.dumps({"python":platform.python_version(),"checks":best_of_two(),"status":"PASS","limitation":"Finite checks do not prove universal statements."},indent=2))
