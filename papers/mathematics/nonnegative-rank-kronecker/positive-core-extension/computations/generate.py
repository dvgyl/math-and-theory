#!/usr/bin/env python3
"""Exact rational check of the explicit positive Kronecker rank-cancellation family.

Uses only the Python standard library. This verifies the displayed factorization,
positivity and ordinary ranks; the seed's nonnegative-rank lower bound uses the
separate nested-squares theorem and is not inferred from these arithmetic checks.
"""
from fractions import Fraction as F
from pathlib import Path
import argparse
import json


def require(condition, message):
    if not condition:
        raise ValueError(message)


def shape(a):
    require(isinstance(a, list) and len(a) > 0, "empty or invalid matrix")
    require(all(isinstance(row, list) for row in a), "invalid row")
    n = len(a[0])
    require(n > 0 and all(len(row) == n for row in a), "ragged or empty matrix")
    require(all(isinstance(x, F) for row in a for x in row), "non-rational matrix entry")
    return len(a), n


def mat(m, n, f=lambda i, j: 0):
    return [[F(f(i, j)) for j in range(n)] for i in range(m)]


def mul(a, b):
    _, an = shape(a)
    bm, _ = shape(b)
    require(an == bm, "matrix product dimension mismatch")
    cols = list(zip(*b))
    return [[sum((x * y for x, y in zip(row, col)), F(0)) for col in cols] for row in a]


def add(a, b):
    require(shape(a) == shape(b), "matrix sum dimension mismatch")
    return [[x + y for x, y in zip(ar, br)] for ar, br in zip(a, b)]


def scale(c, a):
    return [[c * x for x in row] for row in a]


def kron(a, b):
    return [[x * y for x in ar for y in br] for ar in a for br in b]


def rank(a):
    a = [row[:] for row in a]
    r = 0
    for j in range(len(a[0])):
        pivot = next((i for i in range(r, len(a)) if a[i][j]), None)
        if pivot is None:
            continue
        a[r], a[pivot] = a[pivot], a[r]
        for i in range(len(a)):
            if i != r and a[i][j]:
                f = a[i][j] / a[r][j]
                a[i] = [x - f * y for x, y in zip(a[i], a[r])]
        r += 1
    return r


def minimum(a):
    return min(x for row in a for x in row)


def generate(s):
    require(s >= 2, 'exact certificate condition at generator stage 74')
    q = 3 * (s - 1)
    t = mat(4, 4, lambda i, j: 1 if (j - i) % 4 in (0, 1) else -1)
    p = mat(4, 4, lambda i, j: F(1, 2) * ((i == j) - ((j - i) % 4 == 2)))
    a = add(mat(4, 4, lambda i, j: 1), scale(F(9, 20), t))
    u = add(mat(4, 4, lambda i, j: 1), scale(F(19, 20), t))
    v = add(mat(4, 4, lambda i, j: F(1, 4)), scale(F(9, 19), p))
    z = mat(4, 1, lambda i, j: (-1) ** i)
    w = mat(1, 4, lambda i, j: F((-1) ** j, 4))
    require(mul(u, v) == a, 'exact certificate condition at generator stage 83')
    require(mul(u, z) == mat(4, 1), 'exact certificate condition at generator stage 84')
    require(mul(w, v) == mat(1, 4), 'exact certificate condition at generator stage 85')
    require(mul(w, z) == [[1]], 'exact certificate condition at generator stage 86')
    require((rank(a), rank(u), rank(v)) == (3, 3, 3), 'exact certificate condition at generator stage 87')
    require(minimum(u) == F(1, 20) and minimum(v) == F(1, 76), 'exact certificate condition at generator stage 88')

    d = mat(4, q + 3, lambda i, j: (i == 0 if j < q else i == j - q + 1))
    e = mat(q + 3, 4, lambda i, j: (F(j == 0, q) if i < q else j == i - q + 1))
    require(mul(d, e) == mat(4, 4, lambda i, j: i == j), 'exact certificate condition at generator stage 92')
    r = mat(q + 3, q - 1, lambda i, j: (i == j) - (i == q - 1))
    sh = mat(q - 1, q + 3, lambda i, j: (i == j) - (F(1, q) if j < q else 0))
    latent_z = [x + y for x, y in zip(mul(e, z), r)]
    latent_w = mul(w, d) + sh
    up, vp = mul(u, d), mul(e, v)
    require(mul(up, latent_z) == mat(4, q), 'exact certificate condition at generator stage 98')
    require(mul(latent_w, vp) == mat(q, 4), 'exact certificate condition at generator stage 99')
    require(mul(latent_w, latent_z) == mat(q, q, lambda i, j: i == j), 'exact certificate condition at generator stage 100')
    require(max(abs(x) for row in latent_z + latent_w for x in row) <= 1, 'exact certificate condition at generator stage 101')

    ra = [row[:3] for row in a]
    ta = [[F(x) for x in row] for row in [[1, 0, 0, 1], [0, 1, 0, -1], [0, 0, 1, 1]]]
    require(mul(ra, ta) == a, 'exact certificate condition at generator stage 105')
    ws = mat(s, s - 1, lambda i, j: -1 if i == s - 1 else i == j)
    zs = mat(s - 1, s, lambda i, j: (i == j) - F(1, s))
    require(mul(ws, zs) == mat(s, s, lambda i, j: (i == j) - F(1, s)), 'exact certificate condition at generator stage 108')
    x, y = kron(ra, ws), kron(ta, zs)
    eta, eps = F(1, 58 * q), F(1, 8816 * q ** 3)
    beta = 1 + eps / s
    left = add(kron(up, mat(s, 1, lambda i, j: 1)), scale(eta, mul(x, latent_w)))
    right = add(scale(beta, kron(vp, mat(1, s, lambda i, j: 1))), scale(eps / eta, mul(latent_z, y)))
    b = mat(s, s, lambda i, j: 1 + (eps if i == j else 0))
    target = kron(a, b)
    require(mul(left, right) == target, 'exact certificate condition at generator stage 116')
    require(minimum(left) >= F(1, 40), 'exact certificate condition at generator stage 117')
    require(minimum(right) >= F(1, 152 * q), 'exact certificate condition at generator stage 118')
    require(rank(b) == s and rank(target) == 3 * s, 'exact certificate condition at generator stage 119')
    data = {"s": s, "q": q, "epsilon": str(eps), "eta": str(eta), "beta": str(beta),
            "A": a, "B": b, "L": left, "R": right,
            "U": u, "V": v, "D": d, "E": e,
            "U_duplicated": up, "V_duplicated": vp,
            "latent_Z": latent_z, "latent_W": latent_w,
            "X": x, "Y": y, "rank_factor_left_A": ra,
            "rank_factor_right_A": ta,
            "centered_identity_left": ws, "centered_identity_right": zs}
    result = {"status": "PASS", "s": s, "q": q, "epsilon": str(eps),
              "factor_width": len(right), "rank_A": rank(a), "rank_B": rank(b),
              "rank_product": rank(target), "minimum_L": str(minimum(left)),
              "minimum_R": str(minimum(right)), "entries_checked": (4 * s) ** 2}
    return data, result


def encode(value):
    if isinstance(value, F):
        return str(value)
    raise TypeError(type(value))


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--s", type=int, nargs="+", default=[2, 3, 5])
    parser.add_argument("--write", type=Path)
    args = parser.parse_args()
    results = []
    for s in args.s:
        data, result = generate(s)
        results.append(result)
        if args.write:
            args.write.mkdir(parents=True, exist_ok=True)
            (args.write / f"activation_s{s}.json").write_text(json.dumps(data, default=encode, indent=2) + "\n")
    print(json.dumps(results, indent=2))
