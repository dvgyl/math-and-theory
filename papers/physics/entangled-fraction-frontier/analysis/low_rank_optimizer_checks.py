"""Exact, small construction checks for low_rank_optimizer.tex.

These tests check the explicit certificates; they do not substitute for the
compactness and perturbation proof or claim a Lean rank formalization.
"""
from __future__ import annotations

import json
from pathlib import Path

import sympy as s


def ptr_a(matrix, m, n):
    return s.Matrix(m, m, lambda i, k: sum(matrix[i*n+j, k*n+j] for j in range(n)))


def ptr_b(matrix, m, n):
    return s.Matrix(n, n, lambda j, l: sum(matrix[i*n+j, i*n+l] for i in range(m)))


def equal(left, right):
    return all(s.simplify(z) == 0 for z in left - right)


def principal_minors_nonnegative(matrix):
    from itertools import combinations
    for size in range(1, matrix.rows + 1):
        for indices in combinations(range(matrix.rows), size):
            assert matrix.extract(indices, indices).det() >= 0


records = []
delta = s.Rational(2, 7)
for r in range(1, 6):
    for t in range(1, 6):
        q = max(r, t)
        av = [s.Integer(i+1) for i in range(r)]
        bv = [s.Integer(j+2) for j in range(t)]
        sa, sb = sum(x*x for x in av), sum(y*y for y in bv)
        a = [delta*x*x/sa for x in av]
        b = [delta*y*y/sb for y in bv]
        vectors = []
        for shift in range(q):
            z = s.zeros(r*t, 1)
            for i in range(r):
                j = (i+shift) % q
                if j < t:
                    z[i*t+j] = av[i]*bv[j]
            vectors.append(z)
        mat = delta/(sa*sb)*sum((z*z.T for z in vectors), s.zeros(r*t))
        assert equal(ptr_a(mat, r, t), s.diag(*a))
        assert equal(ptr_b(mat, r, t), s.diag(*b))
        assert mat.trace() == delta
        assert mat.rank() == q
        assert all(z != s.zeros(r*t, 1) for z in vectors)
        assert all((vectors[i].T*vectors[j])[0] == 0
                   for i in range(q) for j in range(q) if i != j)
        # The factorization itself is an exact positivity certificate.
        gram = s.Matrix.hstack(*vectors)
        assert equal(mat, delta/(sa*sb)*gram*gram.T)
        records.append({"test": "cyclic_coupling", "r": r, "s": t,
                        "rank": q, "passed": True})

# Independently compare exact complex product ensembles to matching blocks.
roots = {1: s.Integer(1), 2: s.Integer(-1),
         3: (-1+s.I*s.sqrt(3))/2, 4: s.I}
for q, root in roots.items():
    r, t = q, max(1, q-1)
    av = [s.Integer(i+1) for i in range(r)]
    bv = [s.Integer(j+2) for j in range(t)]
    sa, sb = sum(x*x for x in av), sum(y*y for y in bv)
    fourier = s.zeros(r*t)
    cyclic = s.zeros(r*t)
    for h in range(q):
        product = s.Matrix([av[i]*bv[j]*root**(h*(i-j))
                            for i in range(r) for j in range(t)])
        fourier += delta/(q*sa*sb)*product*product.conjugate().T
        z = s.zeros(r*t, 1)
        for i in range(r):
            j = (i+h) % q
            if j < t:
                z[i*t+j] = av[i]*bv[j]
        cyclic += delta/(sa*sb)*z*z.T
    assert equal(fourier, cyclic)
    records.append({"test": "fourier_separable_identity", "q": q,
                    "passed": True})

# Explicit two-sided perturbation of an optimal but non-maximal-norm core.
w = s.Matrix([[s.Rational(1, 2), 0], [0, s.Rational(1, 2)], [0, 0]])
a = s.diag(s.Rational(5, 12), s.Rational(5, 12), s.Rational(1, 6))
c = s.diag(s.Rational(3, 4), s.Rational(1, 4))
y = s.zeros(3, 2)
y[2, 0] = 1
eps = s.Rational(1, 10)
for sign in (-1, 1):
    perturbed = w + sign*eps*y
    principal_minors_nonnegative(a - perturbed*perturbed.T)
    principal_minors_nonnegative(c - perturbed.T*perturbed)
    assert perturbed[1, 1] == s.Rational(1, 2)
    assert (perturbed.T*perturbed).trace() == s.Rational(51, 100)
assert (w.T*w).trace() == s.Rational(1, 2)
records.append({"test": "support_preserving_two_sided_perturbation",
                "old_norm_squared": "1/2", "new_norm_squared": "51/100",
                "target_overlap_squared": "1/4", "passed": True})

# Unique rank-max(m,n) sharpness family: exact matrix, marginals and overlap.
for m in range(2, 6):
    for n in range(1, m+1):
        residual_mass = s.Rational(1, 3)
        mu = (1-residual_mass)/n
        diagonal_vector = s.zeros(m*n, 1)
        for i in range(n):
            diagonal_vector[i*n+i] = 1
        e = s.diag(0, *([residual_mass/(m-1)]*(m-1)))
        bob0 = s.zeros(n)
        bob0[0, 0] = 1
        rho = mu*diagonal_vector*diagonal_vector.T + s.kronecker_product(e, bob0)
        a = s.diag(*([mu]*n + [s.Integer(0)]*(m-n))) + e
        b = mu*s.eye(n) + residual_mass*bob0
        assert equal(ptr_a(rho, m, n), a)
        assert equal(ptr_b(rho, m, n), b)
        assert rho.trace() == 1
        assert all(a[i, i] > 0 for i in range(m))
        assert all(b[j, j] > 0 for j in range(n))
        assert rho.rank() == m
        overlap = (diagonal_vector.T*rho*diagonal_vector)[0]/n
        assert overlap == 1-residual_mass
        assert all(min(a[i, i], b[i, i]) == mu for i in range(n))
        records.append({"test": "unique_optimizer_sharpness_family", "m": m, "n": n,
                        "rank": m, "overlap": str(overlap), "passed": True})

# d=4 simultaneous witness: rank-three state, rank-two separable residual.
d = 4
z = s.zeros(d*d, 1)
for i, value in enumerate((4, 3, 2, 1)):
    z[i*d+i] = s.Rational(value, 6)
residual = s.zeros(d*d)
for alice, bob in (((0, 1), (2, 3)), ((0, 3), (2, 1))):
    vector = s.zeros(d*d, 1)
    vector[alice[0]*d+alice[1]] = 1
    vector[bob[0]*d+bob[1]] = 1
    residual += s.Rational(1, 24)*vector*vector.T
rho = z*z.T + residual
a = s.diag(*[s.Rational(x, 36) for x in (19, 9, 7, 1)])
b = s.diag(*[s.Rational(x, 36) for x in (16, 12, 4, 4)])
assert equal(ptr_a(rho, d, d), a)
assert equal(ptr_b(rho, d, d), b)
assert rho.rank() == 3
assert residual.rank() == 2
for weights in ((1, 1, 1, 1), (1, 2, 3, 4), (1, 0, 0, 0)):
    target = s.zeros(d*d, 1)
    for i, value in enumerate(weights):
        target[i*d+i] = value
    norm2 = sum(v*v for v in weights)
    overlap = (target.T*rho*target)[0]/norm2
    expected = (target.T*z)[0]**2/norm2
    assert overlap == expected
records.append({"test": "simultaneous_d4_coherent_minimum",
                "state_rank": 3, "separable_residual_rank": 2,
                "maximally_entangled_overlap": "25/36", "passed": True})

result = {"arithmetic": "Exact SymPy rational/algebraic arithmetic; no numeric tolerances",
          "scope": "Explicit construction and perturbation certificates; not a formal rank proof",
          "all_passed": all(r["passed"] for r in records),
          "case_count": len(records), "cases": records}
destination = Path(__file__).with_name("low_rank_optimizer_check_results.json")
destination.write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps({"all_passed": result["all_passed"], "case_count": len(records),
                  "output": str(destination)}))
