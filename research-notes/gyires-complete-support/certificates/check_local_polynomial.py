#!/usr/bin/env python3
"""Check finite polynomial identities with exact rational arithmetic."""

if not __debug__:
    raise RuntimeError("Certificate checks require assertions. Run Python without -O or PYTHONOPTIMIZE.")

from collections import defaultdict
from fractions import Fraction as F
from itertools import product
import json
from math import factorial
from pathlib import Path


def multiply(p, q):
    result = defaultdict(F)
    for a, x in p.items():
        for b, y in q.items():
            result[tuple(i + j for i, j in zip(a, b))] += x * y
    return {a: x for a, x in result.items() if x}


def add(p, q, scale=F(1)):
    result = defaultdict(F, p)
    for a, x in q.items():
        result[a] += scale * x
    return {a: x for a, x in result.items() if x}


def linear(values):
    return {tuple(int(i == j) for i in range(len(values))): F(x)
            for j, x in enumerate(values) if x}


def power(p, degree):
    n = len(next(iter(p)))
    result = {(0,) * n: F(1)}
    for _ in range(degree):
        result = multiply(result, p)
    return result


def norm(p):
    total = F(0)
    for a, x in p.items():
        weight = 1
        for exponent in a:
            weight *= factorial(exponent)
        total += weight * x * x
    return total


def derivative(p, j):
    result = {}
    for alpha, value in p.items():
        if alpha[j]:
            beta = list(alpha)
            beta[j] -= 1
            result[tuple(beta)] = alpha[j] * value
    return result


def deletion(p, j):
    return {a[:j] + a[j + 1:]: x for a, x in p.items() if a[j] == 1}


def value_one(p):
    return sum(p.values(), F(0))


def hessian(p):
    n = len(next(iter(p)))
    return [[value_one(derivative(derivative(p, i), j)) for j in range(n)] for i in range(n)]


def determinant3(a):
    return (a[0][0] * (a[1][1] * a[2][2] - a[1][2] * a[2][1])
            - a[0][1] * (a[1][0] * a[2][2] - a[1][2] * a[2][0])
            + a[0][2] * (a[1][0] * a[2][1] - a[1][1] * a[2][0]))


def matvec(a, v):
    return [sum((x * y for x, y in zip(row, v)), F(0)) for row in a]


def dot(v, w):
    return sum((x * y for x, y in zip(v, w)), F(0))


def check_tangent(n, label, b):
    m = n - 1
    c, cm, g = F(factorial(n), n ** n), F(factorial(m), m ** m), F(m, n) ** m
    q = defaultdict(F)
    for i, j in product(range(n), repeat=2):
        alpha = [0] * n
        alpha[i] += 1
        alpha[j] += 1
        q[tuple(alpha)] -= b[i][j]
    h = multiply(power(linear([F(1, n)] * n), n - 2), q)
    trace = sum((b[i][i] for i in range(n)), F(0))
    trace_square = sum((x * x for row in b for x in row), F(0))
    diag_square = sum((b[i][i] ** 2 for i in range(n)), F(0))
    assert all(sum(row) == 0 for row in b)
    assert value_one(h) == 0
    assert all(value_one(derivative(h, j)) == 0 for j in range(n))
    assert norm(h) == c * F(2 * n, m) * trace_square
    assert h[(1,) * n] == c * F(n, m) * trace
    qsum, asum = F(0), F(0)
    for j in range(n):
        s = deletion(h, j)
        a = value_one(s)
        v = [value_one(derivative(s, i)) - a for i in range(m)]
        assert a == F(m, n) ** (n - 3) * b[j][j]
        asum += a
        qsum += norm(s) - 2 * cm * dot(v, v)
    observed = qsum / (n * g * c) - norm(h) / c
    predicted = (F(n * n * (3 * n * n - 5 * n + 4), m ** 5) * diag_square
                 - F(2 * n * (2 * n - 1), m ** 3) * trace_square)
    assert observed == predicted
    assert 2 * asum / (n * g) == F(2 * n, m * m) * trace
    if n >= 3:
        assert observed < 0
    return {"n": n, "direction": label, "norm": str(norm(h)), "deletion_quadratic": str(observed)}


def main():
    records = []
    for n in range(2, 9):
        v = [F(1), F(-1)] + [F(0)] * (n - 2)
        w = [F(2 * i - n + 1) for i in range(n)]
        matrices = {
            "rank_one": [[v[i] * v[j] for j in range(n)] for i in range(n)],
            "contrast_projection": [[F(i == j) - F(1, n) for j in range(n)] for i in range(n)],
            "sum_of_two_squares": [[v[i] * v[j] + F(1, 3) * w[i] * w[j] for j in range(n)] for i in range(n)]}
        for label, b in matrices.items():
            records.append(check_tangent(n, label, b))
    r3 = power(linear([F(1, 3)] * 3), 3)
    v = multiply(multiply(linear([1, -1, 0]), linear([0, 1, -1])), linear([-1, 0, 1]))
    assert norm(v) == 12 and v.get((1, 1, 1), 0) == 0
    for j in range(3):
        q0, q1 = deletion(r3, j), deletion(v, j)
        a0, b0, c0 = (q0.get(alpha, 0) for alpha in [(2, 0), (1, 1), (0, 2)])
        a1, b1, c1 = (q1.get(alpha, 0) for alpha in [(2, 0), (1, 1), (0, 2)])
        assert b0 * b0 + 4 * a0 * c0 == F(8, 81)
        assert 2 * b0 * b1 + 4 * (a0 * c1 + a1 * c0) == 0
        assert b1 * b1 + 4 * a1 * c1 == -4
    assert -4 - F(4, 9) * 12 == F(-28, 3)
    p = multiply(multiply(linear([0, 2, 4]), linear([2, 3, 1])), linear([4, 1, 1]))
    h = {a: x / 8 for a, x in multiply(linear([0, 1, 1]), power(linear([2, 1, 1]), 2)).items()}
    for poly, total in [(p, 216), (h, 4)]:
        assert value_one(poly) == total
        assert all(value_one(derivative(poly, j)) == total for j in range(3))
    residual = add(p, h, -1)
    assert all(x > 0 for x in residual.values())
    matrix = hessian(derivative(residual, 0))
    assert matrix == [[0, 31, 63], [31, 55, 67], [63, 67, 47]]
    assert determinant3(matrix) == -1760
    null_vector = list(map(F, [-11, 16, -8]))
    assert matvec(hessian(derivative(p, 0)), null_vector) == [0, 0, 0]
    assert dot(null_vector, matvec(hessian(derivative(h, 0)), null_vector)) == -112
    derivative_ratio = (F(1, 24) * F(1, 4) - F(1, 8) * F(1, 8)) / (F(4, 9) * F(1, 4) ** 2)
    assert derivative_ratio == F(-3, 16)
    report = {"all_checks_passed": True, "arithmetic": "exact fractions; no floating-point tolerances",
              "scope": "finite identities and examples; not a proof of a global inequality",
              "tangent_records": records,
              "example_checks": ["Vandermonde perturbation", "failed boundary subtraction", "mixing derivative"]}
    Path("local-polynomial-exact-results.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"all_checks_passed": True, "tangent_cases": len(records), "example_checks": report["example_checks"]}))


if __name__ == "__main__":
    main()
