#!/usr/bin/env python3
"""Exact rational checks of the identities, not a proof of the open inequality."""

if not __debug__:
    raise RuntimeError("Certificate checks require assertions. Run Python without -O or PYTHONOPTIMIZE.")

from fractions import Fraction as F
from itertools import permutations
from math import comb, factorial, prod
import json


def permanent(a):
    return sum((prod(a[i][j] for i, j in enumerate(s))
                for s in permutations(range(len(a)))), F(0))


def poisson_binomial(parameters):
    p = [F(1)]
    for x in parameters:
        q = [F(0)] * (len(p) + 1)
        for k, value in enumerate(p):
            q[k] += value * (1-x)
            q[k+1] += value * x
        p = q
    return p


def joint(n, theta, kappa):
    q00 = (1-theta)**2 + kappa*theta*(1-theta)
    q10 = theta*(1-theta)*(1-kappa)
    q11 = theta**2 + kappa*theta*(1-theta)
    j = {(0, 0): F(1)}
    for _ in range(n):
        new = {}
        for (k, ell), value in j.items():
            for dk, dl, weight in [(0, 0, q00), (1, 0, q10),
                                   (0, 1, q10), (1, 1, q11)]:
                key = (k+dk, ell+dl)
                new[key] = new.get(key, F(0)) + value*weight
        j = new
    return j


def check(x, y):
    n = len(x)
    t = sum(x)
    assert sum(y) == t and 0 < t < n
    theta = t/n
    a = [[xi*yj/t+(1-xi)*(1-yj)/(n-t) for yj in y] for xi in x]
    assert all(sum(row) == 1 for row in a)
    assert all(sum(a[i][j] for i in range(n)) == 1 for j in range(n))
    gram = [[sum(a[i][k]*a[j][k] for k in range(n))
             for j in range(n)] for i in range(n)]
    px, py = poisson_binomial(x), poisson_binomial(y)
    b = [F(comb(n, k))*theta**k*(1-theta)**(n-k)
         for k in range(n+1)]
    r = [p/base for p, base in zip(px, b)]
    s = [p/base for p, base in zip(py, b)]
    c = F(factorial(n), n**n)
    cross = sum(bk*rk*sk for bk, rk, sk in zip(b, r, s))
    assert permanent(a)/c == cross
    kappa = (n*sum(yj*yj for yj in y)-t*t)/(t*(n-t))
    variance = sum(py[k]*(k-t)**2 for k in range(n+1))
    assert kappa == 1-variance/(t*(1-t/n))
    j = joint(n, theta, kappa)
    norm = sum(value*r[k]*r[ell] for (k, ell), value in j.items())
    assert permanent(gram)/c == norm
    xp = [theta+kappa*(xi-theta) for xi in x]
    pxp = poisson_binomial(xp)
    for ell in range(n+1):
        assert sum(px[k]*j[k, ell]/b[k] for k in range(n+1)) == pxp[ell]
    return {'n': n, 'mean': str(t), 'kappa': str(kappa),
            'normalized_permanent': str(cross),
            'normalized_gram_permanent': str(norm),
            'identities_exact': True}


def det3(h):
    return (h[0][0]*(h[1][1]*h[2][2]-h[1][2]*h[2][1])
            - h[0][1]*(h[1][0]*h[2][2]-h[1][2]*h[2][0])
            + h[0][2]*(h[1][0]*h[2][1]-h[1][1]*h[2][0]))


if __name__ == '__main__':
    tests = [
        ([F(1), F(1,3), F(1,3)], [F(0), F(2,3), F(1)]),
        ([F(0), F(1,3), F(2,3), F(1)],
         [F(1,4), F(1,4), F(3,4), F(3,4)]),
        ([F(0), F(1,4), F(1,2), F(3,4), F(1)],
         [F(1,5), F(2,5), F(1,2), F(3,5), F(4,5)])
    ]
    reports = [check(x, y) for x, y in tests]
    h = [[0,31,63], [31,55,67], [63,67,47]]
    assert det3(h) == -1760 and sum(h[i][i] for i in range(3)) == 102
    out = {'scope': 'exact checks of normalization identities on three examples; '
                    'not a proof of the remaining two-interval inequality',
           'rank_two_checks': reports,
           'subtraction_obstruction': {'determinant': det3(h), 'trace': 102}}
    with open('rank2_identity_check.json', 'w') as f:
        json.dump(out, f, indent=2)
    print(json.dumps(out, indent=2))
