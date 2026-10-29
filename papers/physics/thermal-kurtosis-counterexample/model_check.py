#!/usr/bin/env python3
"""Exact, dependency-free verification of a three-state thermal model.

Python >= 3.9; uses only the standard library. Run:
    python model_check.py

This checks the finite arithmetic and the cumulant derivative certificates.
It is not a replacement for the analytic eigenbranch proof or Lean verification.
"""
from fractions import Fraction as F
from itertools import permutations
from math import comb
import json

Q = [[F(-11), F(10), F(1)],
     [F(20), F(-52), F(32)],
     [F(32), F(1), F(-33)]]
HOT = [[F(-10), F(10), F(0)],
       [F(20), F(-20), F(0)],
       [F(0), F(0), F(0)]]
COLD = [[F(-1), F(0), F(1)],
        [F(0), F(-32), F(32)],
        [F(32), F(1), F(-33)]]
ENERGY = [F(0), F(2), F(1)]
# beta_hot=(log 2)/2 and beta_cold=5 log 2.
BETA_OVER_LOG2 = [F(1, 2), F(5)]
PI = [F(1684, 2387), F(331, 2387), F(372, 2387)]
C = [None,
     F(2920, 341),
     F(447871920, 39651821),
     F(43039276005280, 4610753397701),
     F(-833027515829480640, 3753001110866489867)]


def dot(a, b):
    return sum((x*y for x, y in zip(a, b)), F(0))


def mv(a, x):
    return [dot(row, x) for row in a]


def solve(a, b):
    """Exact Gaussian elimination; rejects a singular matrix."""
    n = len(b)
    m = [[F(v) for v in row] + [F(rhs)] for row, rhs in zip(a, b)]
    for col in range(n):
        pivot = next(row for row in range(col, n) if m[row][col])
        m[col], m[pivot] = m[pivot], m[col]
        scale = m[col][col]
        m[col] = [v / scale for v in m[col]]
        for row in range(n):
            if row != col:
                scale = m[row][col]
                m[row] = [v-scale*w for v, w in zip(m[row], m[col])]
    return [row[-1] for row in m]


# Polynomials in z and Laurent polynomials in t, represented by exponent pairs.
def add(a, b):
    out = dict(a)
    for monomial, coefficient in b.items():
        out[monomial] = out.get(monomial, F(0)) + coefficient
        if out[monomial] == 0:
            del out[monomial]
    return out


def mul(a, b):
    out = {}
    for (az, at), av in a.items():
        for (bz, bt), bv in b.items():
            key = (az+bz, at+bt)
            out[key] = out.get(key, F(0)) + av*bv
    return {k: v for k, v in out.items() if v}


def det(a):
    out = {}
    for permutation in permutations(range(len(a))):
        inversions = sum(permutation[i] > permutation[j]
                         for i in range(len(a)) for j in range(i+1, len(a)))
        term = {(0, 0): F((-1)**inversions)}
        for i, j in enumerate(permutation):
            term = mul(term, a[i][j])
        out = add(out, term)
    return out


def check():
    # Generator properties and bath decomposition.
    for i in range(3):
        if not (sum(Q[i]) == 0):
            raise ValueError('Mathematical check failed: sum(Q[i]) == 0')
        if not (sum(HOT[i]) == 0 and sum(COLD[i]) == 0):
            raise ValueError('Mathematical check failed: sum(HOT[i]) == 0 and sum(COLD[i]) == 0')
        for j in range(3):
            if not (Q[i][j] == HOT[i][j] + COLD[i][j]):
                raise ValueError('Mathematical check failed: Q[i][j] == HOT[i][j] + COLD[i][j]')
            if i != j:
                if not (Q[i][j] > 0):
                    raise ValueError('Mathematical check failed: Q[i][j] > 0')
                if not (HOT[i][j] >= 0 and COLD[i][j] >= 0):
                    raise ValueError('Mathematical check failed: HOT[i][j] >= 0 and COLD[i][j] >= 0')
    if not (all((p > 0 for p in PI)) and sum(PI) == 1):
        raise ValueError('Mathematical check failed: all((p > 0 for p in PI)) and sum(PI) == 1')
    if not (all((sum((PI[i] * Q[i][j] for i in range(3))) == 0 for j in range(3)))):
        raise ValueError('Mathematical check failed: all((sum((PI[i] * Q[i][j] for i in range(3))) == 0 for j in range(3)))')
    if not (all((beta > 0 for beta in BETA_OVER_LOG2))):
        raise ValueError('Mathematical check failed: all((beta > 0 for beta in BETA_OVER_LOG2))')
    if not (len(set(ENERGY)) == 3):
        raise ValueError('Mathematical check failed: len(set(ENERGY)) == 3')

    # Exact local detailed balance, with base-2 Boltzmann factors. For an absent
    # bath channel both rates vanish; the multiplicative balance equation is 0=0.
    for bath, beta in zip([HOT, COLD], BETA_OVER_LOG2):
        for i in range(3):
            for j in range(3):
                if i == j:
                    continue
                if not ((bath[i][j] == 0) == (bath[j][i] == 0)):
                    raise ValueError('Mathematical check failed: (bath[i][j] == 0) == (bath[j][i] == 0)')
                if bath[i][j] != 0:
                    exponent = -beta*(ENERGY[j]-ENERGY[i])
                    if not (exponent.denominator == 1):
                        raise ValueError('Mathematical check failed: exponent.denominator == 1')
                    if not (bath[i][j] == bath[j][i] * F(2) ** exponent.numerator):
                        raise ValueError('Mathematical check failed: bath[i][j] == bath[j][i] * F(2) ** exponent.numerator')

    # Direct symbolic determinant of zI-Q_theta, t=exp(theta).
    matrix = [[{(1, 0): F(1), (0, 0): F(11)}, {(0, 0): F(-10)}, {(0, -1): F(-1)}],
              [{(0, 0): F(-20)}, {(1, 0): F(1), (0, 0): F(52)}, {(0, 1): F(-32)}],
              [{(0, 1): F(-32)}, {(0, -1): F(-1)}, {(1, 0): F(1), (0, 0): F(33)}]]
    expected = {(3, 0): F(1), (2, 0): F(96), (1, 0): F(2387),
                (0, 0): F(10260), (0, 2): F(-10240), (0, -2): F(-20)}
    if not (det(matrix) == expected):
        raise ValueError('Mathematical check failed: det(matrix) == expected')
    if not (96 ** 2 - 4 * 2387 == -332):
        raise ValueError('Mathematical check failed: 96 ** 2 - 4 * 2387 == -332')

    # Differentiated implicit equation P(chi(theta))=g(theta), at theta=0.
    if not (2387 * C[1] == 20440):
        raise ValueError('Mathematical check failed: 2387 * C[1] == 20440')
    if not (2387 * C[2] + 192 * C[1] ** 2 == 41040):
        raise ValueError('Mathematical check failed: 2387 * C[2] + 192 * C[1] ** 2 == 41040')
    if not (2387 * C[3] + 576 * C[1] * C[2] + 6 * C[1] ** 3 == 81760):
        raise ValueError('Mathematical check failed: 2387 * C[3] + 576 * C[1] * C[2] + 6 * C[1] ** 3 == 81760')
    if not (2387 * C[4] + 768 * C[1] * C[3] + 576 * C[2] ** 2 + 36 * C[1] ** 2 * C[2] == 164160):
        raise ValueError('Mathematical check failed: 2387 * C[4] + 768 * C[1] * C[3] + 576 * C[2] ** 2 + 36 * C[1] ** 2 * C[2] == 164160')
    if not (C[1] > 0 and C[2] > 0 and (C[4] < 0)):
        raise ValueError('Mathematical check failed: C[1] > 0 and C[2] > 0 and (C[4] < 0)')
    kurtosis = C[4]/C[2]
    if not (kurtosis == F(-3470947982622836, 176627429595846691)):
        raise ValueError('Mathematical check failed: kurtosis == F(-3470947982622836, 176627429595846691)')

    # Independent eigenvector derivative recurrence for the directly heat-tilted
    # generator; no conversion from winding cumulants is used here.
    q_deriv = {n: [[F(0) if i == j else COLD[i][j]*(ENERGY[i]-ENERGY[j])**n
                    for j in range(3)] for i in range(3)] for n in range(1, 5)}
    system = [list(row) + [F(-1)] for row in Q] + [PI + [F(0)]]
    vectors = {0: [F(1)]*3}
    computed = {}
    for n in range(1, 5):
        rhs = [F(0)]*3
        for k in range(1, n+1):
            term = mv(q_deriv[k], vectors[n-k])
            rhs = [x-comb(n, k)*y for x, y in zip(rhs, term)]
        for k in range(1, n):
            rhs = [x+comb(n, k)*computed[k]*y
                   for x, y in zip(rhs, vectors[n-k])]
        solution = solve(system, rhs + [F(0)])
        vectors[n] = solution[:3]
        computed[n] = solution[3]
        if not (computed[n] == C[n]):
            raise ValueError('Mathematical check failed: computed[n] == C[n]')
        if not (dot(PI, vectors[n]) == 0):
            raise ValueError('Mathematical check failed: dot(PI, vectors[n]) == 0')
    if not (dot(PI, mv(q_deriv[1], vectors[0])) == C[1]):
        raise ValueError('Mathematical check failed: dot(PI, mv(q_deriv[1], vectors[0])) == C[1]')

    return {"status": "all exact arithmetic checks passed",
            "generator": [[str(x) for x in row] for row in Q],
            "energies": [str(x) for x in ENERGY],
            "beta_over_log2": [str(x) for x in BETA_OVER_LOG2],
            "stationary_distribution": [str(x) for x in PI],
            "heat_cumulants": [str(C[n]) for n in range(1, 5)],
            "heat_cumulants_decimal": [float(C[n]) for n in range(1, 5)],
            "normalized_kurtosis": str(kurtosis),
            "normalized_kurtosis_decimal": float(kurtosis),
            "eigenvector_derivatives": {str(n): [str(x) for x in vectors[n]]
                                        for n in range(1, 5)}}


if __name__ == '__main__':
    print(json.dumps(check(), indent=2))
