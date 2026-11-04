#!/usr/bin/env python3
"""Independent exact verifier for the Kronecker saturation certificates.

No import from the generator, no numerical tolerance, and no assertions.  It
reconstructs the target from the definition, checks all rational entries of the
product, and computes the ordinary rank by exact Gaussian elimination.  This
certifies the product's nonnegative rank exactly, because the factor width and
ordinary rank agree.  The seed's nonnegative-rank-four claim is NOT checked here.
"""

import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path


def require(condition, message):
    if not condition:
        raise ValueError(message)


def read_matrix(data, key, rows, cols):
    raw = data[key]
    require(isinstance(raw, list) and len(raw) == rows, f"{key}: row count")
    out = []
    for row in raw:
        require(isinstance(row, list) and len(row) == cols, f"{key}: column count")
        parsed = []
        for x in row:
            require(isinstance(x, str), f"{key}: noncanonical rational type")
            y = Fraction(x)
            require(str(y) == x, f"{key}: noncanonical rational spelling")
            parsed.append(y)
        out.append(parsed)
    return out


def exact_rank(matrix):
    work = [list(row) for row in matrix]
    row = 0
    pivots = []
    for col in range(len(work[0])):
        pivot = next((k for k in range(row, len(work)) if work[k][col] != 0), None)
        if pivot is None:
            continue
        work[row], work[pivot] = work[pivot], work[row]
        divisor = work[row][col]
        work[row] = [v / divisor for v in work[row]]
        for k in range(row + 1, len(work)):
            factor = work[k][col]
            work[k] = [v - factor * w for v, w in zip(work[k], work[row])]
        pivots.append(col)
        row += 1
        if row == len(work):
            break
    return row, pivots


def verify(path):
    payload = path.read_bytes()
    data = json.loads(payload)
    s = data["s"]
    require(isinstance(s, int) and s >= 2, "s must be an integer at least two")
    q = 3 * (s - 1)
    require(data["q"] == q, "q does not match s")
    epsilon = Fraction(data["epsilon"])
    require(0 < epsilon <= Fraction(1, 8816 * q**3), "epsilon out of certified range")
    a = read_matrix(data, "A", 4, 4)
    b = read_matrix(data, "B", s, s)
    left = read_matrix(data, "L", 4*s, 3*s)
    right = read_matrix(data, "R", 3*s, 4*s)
    for i in range(4):
        for j in range(4):
            expected = Fraction(29 if (j-i) % 4 in (0, 1) else 11, 20)
            require(a[i][j] == expected, "seed differs from the stated definition")
    for i in range(s):
        for j in range(s):
            require(b[i][j] == 1 + (epsilon if i == j else 0), "B differs from J+epsilon I")
    min_left = min(x for row in left for x in row)
    min_right = min(x for row in right for x in row)
    require(min_left >= Fraction(1,40), "left factor fails strict lower bound")
    require(min_right >= Fraction(1,152*q), "right factor fails strict lower bound")
    target = []
    count = 0
    for i in range(4*s):
        row = []
        for j in range(4*s):
            expected = a[i//s][j//s] * b[i%s][j%s]
            actual = sum((left[i][h] * right[h][j] for h in range(3*s)), Fraction())
            require(actual == expected, f"product mismatch at ({i},{j})")
            row.append(expected)
            count += 1
        target.append(row)
    rank_a, _ = exact_rank(a)
    rank_b, _ = exact_rank(b)
    rank_product, pivots = exact_rank(target)
    require(rank_a == 3 and rank_b == s and rank_product == 3*s, "rank check failed")
    return {
        "file": path.name, "sha256": hashlib.sha256(payload).hexdigest(),
        "status": "PASS", "s": s, "epsilon": str(epsilon),
        "factor_width": 3*s, "ordinary_rank_product": rank_product,
        "nonnegative_rank_product_exact": rank_product,
        "product_entries_checked": count, "pivot_columns": pivots,
        "minimum_left": str(min_left), "minimum_right": str(min_right),
        "seed_nonnegative_rank_lower_bound_checked": False,
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("certificates", nargs="+", type=Path)
    args = parser.parse_args()
    print(json.dumps([verify(path) for path in args.certificates], indent=2))
