#!/usr/bin/env python3
"""Exact rational audit of the nine Tiles columns; entropy decimals are illustrative.

No third-party dependency. This is an explanatory calculation, not Lean
verification of an entropy theorem or of an LOCC operational model.
"""

from fractions import Fraction as F
from itertools import combinations
import json
import math


def transpose(a):
    return [list(row) for row in zip(*a)]


def multiply(a, b):
    return [[sum(x * y for x, y in zip(row, col)) for col in zip(*b)]
            for row in a]


def determinant3(a):
    return (a[0][0] * (a[1][1] * a[2][2] - a[1][2] * a[2][1])
            - a[0][1] * (a[1][0] * a[2][2] - a[1][2] * a[2][0])
            + a[0][2] * (a[1][0] * a[2][1] - a[1][1] * a[2][0]))


def h2(p):
    return -p * math.log2(p) - (1 - p) * math.log2(1 - p)


# Same ordering and integer entries as TilesBase.tilesLeft/tilesRight.
left = [(1, 0, 0), (0, 0, 1), (1, -1, 0), (0, 1, -1), (1, 1, 1)]
right = [(1, -1, 0), (0, 1, -1), (0, 0, 1), (1, 0, 0), (1, 1, 1)]
vectors = [[x * y for x in a for y in b] for a, b in zip(left, right)]
weights = [F(1, 2)] * 4 + [F(1, 9)]
p = [[F(i == j) - sum(w * v[i] * v[j] for w, v in zip(weights, vectors))
      for j in range(9)] for i in range(9)]
assert p == transpose(p)
assert multiply(p, p) == p
assert sum(p[i][i] for i in range(9)) == 4

rows = []
ensemble_weight = F(0)
for j in range(9):
    c = [[p[3 * a + b][j] for b in range(3)] for a in range(3)]
    gram = multiply(c, transpose(c))
    norm_sq = sum(gram[i][i] for i in range(3))
    assert norm_sq == p[j][j]
    reduced = [[x / norm_sq for x in row] for row in gram]
    trace = sum(reduced[i][i] for i in range(3))
    second = sum(reduced[a][a] * reduced[b][b] - reduced[a][b] * reduced[b][a]
                 for a, b in combinations(range(3), 2))
    determinant = determinant3(reduced)
    center = j == 4
    assert norm_sq == (F(8, 9) if center else F(7, 18))
    assert trace == 1
    assert determinant == 0
    assert second == (F(1, 16) if center else F(4, 49))
    weight = norm_sq / 4
    ensemble_weight += weight
    rows.append({"cell": divmod(j, 3), "norm_squared": str(norm_sq),
                 "ensemble_weight": str(weight), "reduced_trace": str(trace),
                 "sum_principal_2x2_minors": str(second),
                 "reduced_determinant": str(determinant),
                 "characteristic_polynomial": f"x * (x^2 - x + {second})"})

assert ensemble_weight == 1
domino_lambda = (7 + math.sqrt(33)) / 14
center_lambda = (2 + math.sqrt(3)) / 4
print(json.dumps({
    "exact_rational_checks_passed": True,
    "normalization": "rho = P/4",
    "columns": rows,
    "entropy_bound_exact": "(7/9)*h2((7+sqrt(33))/14) + (2/9)*h2((2+sqrt(3))/4)",
    "entropy_bound_float_bits": (7 / 9) * h2(domino_lambda) + (2 / 9) * h2(center_lambda),
    "float_is_interval_certified": False,
    "lean_entropy_or_locc_formalization": False,
}, indent=2))
