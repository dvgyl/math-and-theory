#!/usr/bin/env python3
"""Independent finite certificate using only Python's exact Fraction type.

This is supplementary reproducibility code. The universal parameterized
theorem is checked by Lean, not inferred from the finite checks here.
"""

from fractions import Fraction as F
from itertools import permutations
import json


def require(condition):
    if not condition:
        raise ArithmeticError("Exact matrix identity failed")


def mat(rows):
    return [[F(x) for x in row] for row in rows]


def eye(n):
    return [[F(i == j) for j in range(n)] for i in range(n)]


def transpose(a):
    return [list(row) for row in zip(*a)]


def add(a, b):
    return [[x + y for x, y in zip(ar, br)] for ar, br in zip(a, b)]


def scale(a, c):
    return [[c * x for x in row] for row in a]


def sub(a, b):
    return add(a, scale(b, F(-1)))


def mul(a, b):
    bt = transpose(b)
    return [[sum((x * y for x, y in zip(ar, bc)), F(0)) for bc in bt] for ar in a]


def qform(a, v):
    return sum((v[i] * a[i][j] * v[j] for i in range(len(v))
                for j in range(len(v))), F(0))


def means(ps):
    n = len(ps)
    d = len(ps[0])
    total = scale(eye(d), F(0))
    for p in ps:
        require(transpose(p) == p)
        require(mul(p, p) == p)
        total = add(total, p)
    arithmetic = scale(total, F(1, n))
    geometric = scale(eye(d), F(0))
    perms = list(permutations(range(n)))
    for order in perms:
        product = eye(d)
        for i in order:
            product = mul(product, ps[i])
        geometric = add(geometric, product)
    geometric = scale(geometric, F(1, len(perms)))
    power = eye(d)
    for _ in range(n):
        power = mul(power, arithmetic)
    return arithmetic, geometric, power


def main():
    vectors = [(-1, 1, 1), (1, -1, 1), (1, 1, -1)]
    ps = [mat([[F(x * y, 3) for y in v] for x in v]) for v in vectors]
    a, g, a3 = means(ps)
    w = [F(1)] * 3
    require(qform(sub(g, a3), w) == F(8, 243))
    require(all(sum(p[i][i] for i in range(3)) == 1 for p in ps))

    identity = eye(3)
    j = mat([[1] * 3 for _ in range(3)])
    require(a == scale(sub(scale(identity, F(4)), j), F(1, 9)))
    require(g == scale(sub(j, scale(identity, F(2))), F(1, 81)))
    require(sub(a3, g) == scale(sub(scale(identity, F(82)), scale(j, F(30))), F(1, 729)))
    require(transpose(g) == g)
    print(json.dumps({
        "arithmetic": "exact rational arithmetic; no floating point",
        "finite_3x3_excess": "8/243",
        "all_projection_identities": True,
        "exact_mean_and_symmetrized_product": True,
        "exact_matrix_difference": True,
        "result": "PASS"
    }, indent=2))


if __name__ == "__main__":
    main()
