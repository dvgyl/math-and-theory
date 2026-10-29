"""Independent exact arithmetic audit of the ADMM five-cycle.

This script restates the published integer inputs and uses only the standard
library.  It does not import the discovery or certificate-generation scripts.
It is an arithmetic audit, not a replacement for the mathematical proof or Lean.
"""

# Assertions are part of this certificate.
import os as _assertion_guard_os
if not __debug__ or "PYTHONOPTIMIZE" in _assertion_guard_os.environ:
    raise SystemExit("Verification requires assertions; remove -O/-OO and unset PYTHONOPTIMIZE.")

from fractions import Fraction as F
from pathlib import Path
import json

Z = (
    (20, -62, -161, 80),
    (-52, -38, 177, 31),
    (-53, 38, -126, -129),
    (20, 62, 26, 178),
    (65, 0, 84, -160),
)
V = (
    (57, -289, 314, -85),
    (-257, -143, -304, -116),
    (-216, 200, 178, 273),
    (124, 267, 16, -325),
    (292, -35, -204, 253),
)
tau, mu = F(199, 100), F(1, 1000)


def dot(a, b):
    return sum(x * y for x, y in zip(a, b))


def sub(a, b):
    return tuple(x - y for x, y in zip(a, b))


def det_elimination(rows):
    m = [[F(x) for x in row] for row in rows]
    out = F(1)
    for i in range(len(m)):
        pivot = next((j for j in range(i, len(m)) if m[j][i]), None)
        if pivot is None:
            return F(0)
        if pivot != i:
            m[i], m[pivot] = m[pivot], m[i]
            out = -out
        p = m[i][i]
        out *= p
        for j in range(i + 1, len(m)):
            ratio = m[j][i] / p
            for k in range(i, len(m)):
                m[j][k] -= ratio * m[i][k]
    return out


X = tuple(tuple(Z[i][j] + V[i][j] - V[(i - 1) % 5][j]
                for j in range(4)) for i in range(5))
U = tuple(tuple(tau * v for v in row) for row in V)
A = tuple(tuple(Z[(i - 1) % 5][j] - U[(i - 1) % 5][j] - X[i][j]
                for j in range(4)) for i in range(5))
B = tuple(tuple(X[i][j] + U[(i - 1) % 5][j] - Z[i][j]
                for j in range(4)) for i in range(5))
Q = tuple(tuple(A[i][j] - mu * X[i][j] for j in range(4)) for i in range(5))
R = tuple(tuple(B[i][j] - mu * Z[i][j] for j in range(4)) for i in range(5))

assert X == ((-215, -316, 357, -258), (-366, 108, -441, 0),
             (-12, 381, 356, 260), (360, 129, -136, -420),
             (233, -302, -136, 418))
for points in (X, Z, V):
    assert all(sum(p[j] for p in points) == 0 for j in range(4))
for i in range(5):
    for j in range(4):
        assert U[i][j] == U[(i - 1) % 5][j] + tau * (X[i][j] - Z[i][j])

normal_margins = [dot(normals[i], sub(points[i], points[j]))
                  for points, normals in ((X, A), (Z, B))
                  for i in range(5) for j in range(5) if i != j]
strong_margins = [dot(normals[i], sub(points[i], points[j]))
                  for points, normals in ((X, Q), (Z, R))
                  for i in range(5) for j in range(5) if i != j]
origin_margins = [dot(normals[i], points[i])
                  for points, normals in ((X, Q), (Z, R)) for i in range(5)]
assert min(normal_margins) == F(136989, 100)
assert min(strong_margins) == F(24286, 25) > 1
assert min(origin_margins) == F(2713619, 125) > 1
residuals = [dot(sub(X[i], Z[i]), sub(X[i], Z[i])) for i in range(5)]
assert min(residuals) >= 500000
assert residuals[0] == 502309
assert len(set(Z)) == 5
det_x = det_elimination([sub(X[i], X[4]) for i in range(4)])
det_z = det_elimination([sub(Z[i], Z[4]) for i in range(4)])
assert det_x == 395537260080
assert det_z == 1913707790

# Every projection normal margin is affine in tau. Derive its coefficients
# directly, independently of the normal arrays A and B at tau=199/100.
affine_margins = []
for label, points in (("C", X), ("D", Z)):
    for i in range(5):
        prev = (i - 1) % 5
        if label == "C":
            const = sub(Z[prev], X[i])
            slope = tuple(-v for v in V[prev])
        else:
            const = sub(X[i], Z[i])
            slope = V[prev]
        for j in range(5):
            if i != j:
                delta = sub(points[i], points[j])
                a, b = dot(const, delta), dot(slope, delta)
                assert b > 0
                affine_margins.append((F(-a, b), label, i, j, a, b))
threshold = max(r[0] for r in affine_margins)
assert threshold == F(140111, 70637)

# Scalar smoothing checks: middle polynomial in s=t+1 is s^3-s^4/2.
# The derivative endpoint data are (value, first derivative, second derivative).
def middle_data(s):
    return (s**3 - s**4 / F(2), 3*s*s - 2*s**3, 6*s*(1-s))

assert middle_data(F(0)) == (0, 0, 0)
assert middle_data(F(1)) == (F(1, 2), 1, 0)
# Coefficient identity: psi(t)-(t+1/2) = (1-s)^3*(1+s)/2.
# Coefficients of powers s^0,...,s^4 on both sides.
left = [F(1, 2), F(-1), F(0), F(1), F(-1, 2)]
factor_a, factor_b = [1, -3, 3, -1], [1, 1]
right = [F(sum(factor_a[i] * factor_b[j]
               for i in range(4) for j in range(2) if i+j == k), 2)
         for k in range(5)]
assert left == right

output = {
    "status": "Independent exact arithmetic checks passed; no numerical optimizer used.",
    "tau": str(tau), "mu": str(mu),
    "normal_margin_count": len(normal_margins),
    "minimum_normal_margin": str(min(normal_margins)),
    "minimum_strong_margin": str(min(strong_margins)),
    "minimum_origin_margin": str(min(origin_margins)),
    "residual_squared": residuals,
    "determinants": [str(det_x), str(det_z)],
    "same_polytopes_tau_threshold": str(threshold),
    "active_thresholds": [r[1:4] for r in affine_margins if r[0] == threshold],
    "all_affine_margin_slopes_strictly_positive": True,
    "smooth_lipschitz_upper_bounds": [str(mu + F(3, 2) * sum(dot(q, q) for q in rows))
                                      for rows in (Q, R)],
    "smooth_scalar_endpoint_and_factorization_checks": "passed",
    "formal_scope": "This script does not claim Lean verification."
}
path = Path(__file__).with_name("admm_independent_exact_audit.json")
path.write_text(json.dumps(output, indent=2) + "\n")
print(json.dumps(output, indent=2))
