#!/usr/bin/env python3
"""Independent finite-difference checks of local formulas; not a general proof."""

if not __debug__:
    raise RuntimeError("Certificate checks require assertions. Run Python without -O or PYTHONOPTIMIZE.")

import json
import math
from collections import defaultdict
from itertools import product

import numpy as np
from scipy.special import logsumexp


def multiply(p, q):
    r = defaultdict(float)
    for a, x in p.items():
        for b, y in q.items():
            r[tuple(i+j for i, j in zip(a, b))] += x*y
    return dict(r)


def uniform_power(n, degree):
    unit = [tuple(int(i == j) for i in range(n)) for j in range(n)]
    linear = {u: 1/n for u in unit}
    p = {(0,)*n: 1.}
    for _ in range(degree):
        p = multiply(p, linear)
    return p


def tangent(n, B):
    Q = defaultdict(float)
    for i in range(n):
        for j in range(n):
            a = [0]*n
            a[i] += 1
            a[j] += 1
            Q[tuple(a)] -= B[i, j]
    return multiply(uniform_power(n, n-2), Q)


def norm(p):
    return sum(math.prod(math.factorial(k) for k in a)*v*v for a, v in p.items())


def deletion_norm(p, j):
    records = [(a[:j]+a[j+1:], v) for a, v in p.items() if a[j] == 1 and v > 0]
    X = np.array([a for a, _ in records], dtype=float)
    logs = np.log([v for _, v in records])
    m = X.shape[1]
    if m == 1:
        return math.exp(2*logs[0])
    Z = X[:, :-1]-X[:, -1:]
    z = np.zeros(m-1)
    for _ in range(40):
        l = logs+Z@z
        f = logsumexp(l)
        w = np.exp(l-f)
        g = w@Z
        if max(abs(g)) < 2e-14:
            break
        H = (Z.T*w)@Z-np.outer(g, g)
        delta = np.linalg.solve(H, -g)
        step = 1.
        while logsumexp(logs+Z@(z+step*delta)) > f+1e-4*step*(g@delta)+1e-15:
            step *= .5
        z += step*delta
    y = np.r_[z, -sum(z)]
    return sum(math.prod(math.factorial(int(k)) for k in a)
               *math.exp(2*lv+2*np.dot(a, y)) for a, lv in zip(X, logs))


def ratio(p):
    n = len(next(iter(p)))
    g = ((n-1)/n)**(n-1)
    return sum(deletion_norm(p, j) for j in range(n))/(n*g*norm(p))


def main():
    records = []
    for n in range(2, 7):
        v = np.zeros(n)
        v[0] = 1
        v[1] = -1
        for label, B in [('rank_one', np.outer(v, v)),
                         ('projection', np.eye(n)-np.ones((n, n))/n)]:
            p0 = uniform_power(n, n)
            h = tangent(n, B)
            c = math.factorial(n)/n**n
            m = n-1
            predicted_norm = c*2*n/m*np.trace(B@B)
            assert abs(norm(h)-predicted_norm) < 1e-12
            predicted_central = c*n/m*np.trace(B)
            assert abs(h[(1,)*n]-predicted_central) < 1e-12
            first = 2*n/m**2*np.trace(B)
            second = (n*n*(3*n*n-5*n+4)/m**5*np.dot(np.diag(B), np.diag(B))
                      -2*n*(2*n-1)/m**3*np.trace(B@B))
            eps = 2e-4
            plus = {a: value+eps*h.get(a, 0) for a, value in p0.items()}
            minus = {a: value-eps*h.get(a, 0) for a, value in p0.items()}
            rp, rm = ratio(plus), ratio(minus)
            observed_first = (rp-rm)/(2*eps)
            observed_second = (rp+rm-2)/(2*eps*eps)
            assert abs(observed_first-first) < 5e-5
            assert abs(observed_second-second) < 5e-5
            records.append({'n': n, 'direction': label,
                            'first_derivative': float(first),
                            'observed_first': float(observed_first),
                            'quadratic_coefficient': float(second),
                            'observed_quadratic': float(observed_second)})
    report = {'purpose': 'check local derivative arithmetic; not a proof',
              'all_checks_passed': True, 'records': records}
    with open('local_check.json', 'w') as f:
        json.dump(report, f, indent=2)
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
