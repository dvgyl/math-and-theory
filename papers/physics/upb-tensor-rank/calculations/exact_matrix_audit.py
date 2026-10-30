#!/usr/bin/env python3
"""Independent integer audit of the explicit Tiles tensor projector.

This checks finite matrix identities. The central rank-two exclusion and
cone nonmembership are proved separately in Lean; this script does not
replace those proofs and makes no novelty claim.
"""
import json
from pathlib import Path


def matmul(a, b):
    bt = list(zip(*b))
    return [[sum(x*y for x, y in zip(row, col)) for col in bt] for row in a]


def main():
    left = [[1, 0, 0], [0, 0, 1], [1, -1, 0], [0, 1, -1], [1, 1, 1]]
    right = [[1, -1, 0], [0, 1, -1], [0, 0, 1], [1, 0, 0], [1, 1, 1]]
    w = [[a*b for a in l for b in r] for l, r in zip(left, right)]
    gram = [[sum(a*b for a, b in zip(u, v)) for v in w] for u in w]
    assert gram == [[([2, 2, 2, 2, 9][i] if i == j else 0)
                     for j in range(5)] for i in range(5)]

    # M = 18 P0, constructed from the five orthogonal product vectors.
    m = [[18*(i == j) - 9*sum(w[k][i]*w[k][j] for k in range(4))
          - 2*w[4][i]*w[4][j] for j in range(9)] for i in range(9)]

    # Independent construction from the four-dimensional kernel basis.
    basis = [[0]*9 for _ in range(4)]
    for k, positions in enumerate([(0, 1), (2, 5), (3, 6), (7, 8)]):
        for p in positions:
            basis[k][p] = 1
        basis[k][4] = -2
    bgram = [[sum(x*y for x, y in zip(u, v)) for v in basis] for u in basis]
    assert bgram == [[2*(i == j) + 4 for j in range(4)] for i in range(4)]
    m_basis = [[9*sum(basis[k][i]*basis[k][j] for k in range(4))
                - 2*sum(basis[k][i] for k in range(4))*
                    sum(basis[k][j] for k in range(4))
                for j in range(9)] for i in range(9)]
    assert m == m_basis
    assert matmul(m, m) == [[18*x for x in row] for row in m]
    assert sum(m[i][i] for i in range(9)) == 72
    for a in range(3):
        for b in range(3):
            for c in range(3):
                for d in range(3):
                    assert m[3*a+b][3*c+d] == m[3*a+d][3*c+b]

    # Ordering is ((A1,A2),(B1,B2)); local dimension is 9 on each side.
    indices = [(a, c, b, d) for a in range(3) for c in range(3)
               for b in range(3) for d in range(3)]
    n = [[m[3*a+b][3*e+f] * m[3*c+d][3*g+h]
          for e, g, f, h in indices] for a, c, b, d in indices]
    assert matmul(n, n) == [[324*x for x in row] for row in n]
    assert all(n[i][j] == n[j][i] for i in range(81) for j in range(81))
    assert sum(n[i][i] for i in range(81)) == 16*324
    assert n[40][40] == 256  # P_{(11),(11)} = (8/9)^2.
    for a in range(9):
        for b in range(9):
            for c in range(9):
                for d in range(9):
                    assert n[9*a+b][9*c+d] == n[9*a+d][9*c+b]

    out = Path(__file__).resolve().parent
    (out / "explicit_matrix.json").write_text(json.dumps({
        "local_dimensions": [9, 9],
        "index_order": "((A1,A2),(B1,B2)), each index lexicographic from 0",
        "denominator": 324,
        "numerator": n,
        "base_denominator": 18,
        "base_numerator": m,
    }, indent=2) + "\n")
    report = {
        "arithmetic": "exact integers; no floating point",
        "five_product_vectors_mutually_orthogonal": True,
        "independent_basis_projection_agrees": True,
        "base_projection": True,
        "base_partial_transpose_invariant": True,
        "base_trace": 4,
        "regrouped_tensor_projection": True,
        "tensor_hermitian": True,
        "tensor_partial_transpose_invariant": True,
        "tensor_trace": 16,
        "tensor_nonzero_entry": "64/81",
        "central_cone_exclusion": "not checked here; see Main.lean and the verification log",
    }
    (out / "exact_matrix_audit.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
