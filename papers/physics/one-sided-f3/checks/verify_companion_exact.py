#!/usr/bin/env python3
"""Independent exact-arithmetic checks of the companion determinant identities.

These checks are regression evidence; the universal proofs are in the Lean
modules and the mathematical manuscript. No numerical root solver is used.
"""
from __future__ import annotations
import json
from pathlib import Path
import random
import sympy as sp


def run() -> dict:
    rng = random.Random(240603945)
    z = sp.Symbol('z')
    cases = 0
    singular_evaluations = 0
    for n in range(1, 5):
        for k in range(12):
            if k < 4:
                entries = [0] * n if k == 0 else [(-1, 0, 1)[(i + k) % 3] for i in range(n)]
                H = sp.diag(*entries)
            else:
                H = sp.Matrix(n, n, [rng.randrange(-3, 4) for _ in range(n * n)])
                if k % 2 == 0:
                    H = H + H.T
            g = sp.zeros(n, 1) if k == 0 else sp.Matrix([rng.randrange(-3, 4) for _ in range(n)])
            I = sp.eye(n)
            C = H.row_join(I).col_join((g * g.T).row_join(H))
            # Independent algorithms: Berkowitz characteristic polynomial of
            # the 2n matrix, versus direct determinant of an n-matrix polynomial.
            lhs = C.charpoly(z).as_expr()
            rhs = (((z * I - H) ** 2) - g * g.T).det(method='domain-ge')
            assert sp.Poly(lhs - rhs, z).is_zero
            assert sp.degree(lhs, z) == 2 * n
            D = H.charpoly(z).as_expr()
            N = (g.T * (z * I - H).adjugate() * g)[0]
            compressed = D ** 2 + D * sp.diff(N, z) - sp.diff(D, z) * N
            assert sp.Poly(lhs - compressed, z).is_zero
            if H.is_diagonal():
                p = sp.prod((z - H[i, i]) ** 2 for i in range(n))
                p -= sum(g[i] ** 2 * sp.prod((z - H[j, j]) ** 2 for j in range(n) if j != i)
                         for i in range(n))
                assert sp.Poly(lhs - p, z).is_zero
                for i in range(n):
                    # Explicit checks at points excluded by inverse-based
                    # determinant arguments: zI-H is singular here.
                    zi = H[i, i]
                    assert (zi * I - H).det() == 0
                    assert (zi * sp.eye(2 * n) - C).det() == rhs.subs(z, zi)
                    singular_evaluations += 1
            cases += 1
    original_invariant_cases = 0
    for k in range(12):
        if k == 0:
            Q = sp.zeros(3)
        elif k == 1:
            Q = sp.diag(2, 0, 0)
        elif k == 2:
            Q = sp.diag(2, 2, 0)
        else:
            M = sp.Matrix(3, 3, [rng.randrange(-2, 3) for _ in range(9)])
            Q = M * M.T
        c = sp.Matrix([sp.Rational(rng.randrange(-3, 4), 5) for _ in range(3)])
        D = Q.charpoly(z).as_expr()
        N = (c.T * Q * (z * sp.eye(3) - Q).adjugate() * c)[0]
        tau = sp.trace(Q)
        s2 = (tau ** 2 - sp.trace(Q ** 2)) / 2
        s3 = Q.det()
        beta = (c.T * c)[0]
        u = (c.T * Q * c)[0]
        v = (c.T * Q ** 2 * c)[0]
        assert sp.Poly(D - (z ** 3 - tau * z ** 2 + s2 * z - s3), z).is_zero
        assert sp.Poly(N - (u * z ** 2 + (v - tau * u) * z + s3 * beta), z).is_zero
        C = Q.row_join(sp.eye(3)).col_join((Q * c * c.T).row_join(Q))
        assert sp.Poly(C.charpoly(z).as_expr() - D ** 2 - D * sp.diff(N, z)
                       + sp.diff(D, z) * N, z).is_zero
        original_invariant_cases += 1
    derivative_cases = 0
    singular_data = [
        ([2, 0, -1], [0, 1, 1], 2),
        ([2, 2, 0], [0, 0, 1], 2),
        ([2, 2, 2], [0, 0, 0], 2),
        ([0, -1, -2], [0, sp.Rational(1, 2), sp.Rational(1, 2)], 0),
        ([0, 0, -1], [0, 0, sp.Rational(1, 2)], 0),
        ([0, 0, 0], [0, 0, 0], 0),
    ]
    for h, gv, mu in singular_data:
        H = sp.diag(*h)
        g = sp.Matrix(gv)
        D = H.charpoly(z).as_expr()
        N = (g.T * (z * sp.eye(3) - H).adjugate() * g)[0]
        r = sum(hi == mu for hi in h)
        assert all(g[i] == 0 for i in range(3) if h[i] == mu)
        assert sum(g[i] ** 2 / (mu - h[i]) ** 2 for i in range(3) if h[i] != mu) <= 1
        assert all(sp.diff(N, z, k).subs(z, mu) == 0 for k in range(r))
        ratio = sp.diff(N, z, r).subs(z, mu) / sp.diff(D, z, r).subs(z, mu)
        expected = sum(g[i] ** 2 / (mu - h[i]) for i in range(3) if h[i] != mu)
        assert sp.simplify(ratio - expected) == 0
        derivative_cases += 1
    return {
        'status': 'PASS',
        'arithmetic': 'exact integer/rational polynomial arithmetic (SymPy)',
        'sympy_version': sp.__version__,
        'seed': 240603945,
        'companion_polynomial_cases': cases,
        'determinant_numerator_compression_cases': cases,
        'singular_derivative_rule_cases': derivative_cases,
        'original_Q_c_invariant_cases': original_invariant_cases,
        'six_scalar_invariant_cases': original_invariant_cases,
        'matrix_dimensions': [1, 2, 3, 4],
        'companion_dimensions': [2, 4, 6, 8],
        'singular_shift_evaluations': singular_evaluations,
        'includes': ['zero g', 'zero H', 'repeated eigenvalues', 'nonsymmetric H', 'symmetric H'],
        'claim': 'Independent exact regression checks; universal claims are proved separately.'
    }


if __name__ == '__main__':
    result = run()
    path = Path(__file__).with_name('companion_exact_results.json')
    path.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))
