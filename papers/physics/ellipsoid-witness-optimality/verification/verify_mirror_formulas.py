#!/usr/bin/env python3
"""Independent exact symbolic verification of the two mirror PSD certificates.

Uses SymPy only. Parameter inequalities, not floating-point eigenvalues, prove
the displayed PSD decompositions. The general normal-form existence theorem
and the cone/orbit arguments are mathematical dependencies, not checked here.
"""

import sympy as s

I2 = s.eye(2)
X = s.Matrix([[0, 1], [1, 0]])
Y = s.Matrix([[0, -s.I], [s.I, 0]])
Z = s.diag(1, -1)
II = s.eye(4)
XX, YY, ZZ = [s.kronecker_product(M, M) for M in (X, Y, Z)]


def projector(v):
    v = s.Matrix(v)
    return v * v.conjugate().T / (v.conjugate().T * v)[0]


phi_p = projector([1, 0, 0, 1])
phi_m = projector([1, 0, 0, -1])
psi_p = projector([0, 1, 1, 0])
psi_m = projector([0, 1, -1, 0])
p01 = projector([0, 1, 0, 0])


def zero(M):
    assert M.applyfunc(s.simplify) == s.zeros(*M.shape), M


def partial_transpose_B(M):
    return s.Matrix(4, 4, lambda i, j: M[(i // 2) * 2 + j % 2,
                                       (j // 2) * 2 + i % 2])


def canonical_ellipse(a, b, T):
    gamma2 = 1 / (1 - b.dot(b))
    c = gamma2 * (a - T * b)
    M = T - a * b.T
    Q = gamma2 * M * (s.eye(3) + gamma2 * b * b.T) * M.T
    return c.applyfunc(s.simplify), Q.applyfunc(s.simplify)


w, x, y, z = s.symbols("w x y z", real=True)
a = x + y - w
ordinary_p = w * II + x * XX + y * YY + z * ZZ
ordinary_m = w * II + x * XX + y * YY - z * ZZ
ordinary_R = w * II + x * XX + y * YY - a * ZZ
zero((a + z) * ordinary_m - (a - z) * ordinary_p - 2 * z * ordinary_R)
zero(ordinary_R - (2 * (w - y) * phi_p + 2 * (w - x) * phi_m
                   + 2 * (x + y) * psi_p))

w, k, r, q = s.symbols("w k r q", positive=True)
product = s.kronecker_product(I2 + Z, I2 - Z)
extra_p = w * (II + ZZ) + k * product + r * XX + q * YY
extra_m = w * (II + ZZ) + k * product + r * XX - q * YY
extra_R = w * (II + ZZ) + k * product + r * (XX - YY)
zero((r + q) * extra_m - (r - q) * extra_p - 2 * q * extra_R)
zero(extra_R - (2 * (w + r) * phi_p + 2 * (w - r) * phi_m + 4 * k * p01))
zero(partial_transpose_B(extra_p) - extra_m)

a_vec = s.Matrix([0, 0, k / (w + k)])
b_vec = -a_vec
T_p = s.diag(r / (w + k), q / (w + k), (w - k) / (w + k))
T_m = s.diag(r / (w + k), -q / (w + k), (w - k) / (w + k))
c_p, Q_p = canonical_ellipse(a_vec, b_vec, T_p)
c_m, Q_m = canonical_ellipse(a_vec, b_vec, T_m)
zero(c_p - c_m)
zero(Q_p - Q_m)
zero(c_p - s.Matrix([0, 0, 2 * k / (w + 2 * k)]))
zero(Q_p - s.diag(r**2 / (w * (w + 2*k)), q**2 / (w * (w + 2*k)),
                  w**2 / (w + 2*k)**2))

# A strictly interior, rational Class-D counterexample to the unqualified iff.
rat = s.Rational
Wp = (II + rat(3, 4) * XX + rat(3, 4) * YY + rat(1, 4) * ZZ) / 4
Wm = (II + rat(3, 4) * XX + rat(3, 4) * YY - rat(1, 4) * ZZ) / 4
P = rat(1, 12) * phi_p + rat(1, 12) * phi_m + rat(1, 2) * psi_p
zero(Wm - rat(1, 3) * Wp - P)
assert Wp.trace() == Wm.trace() == 1
assert Wp.det() < 0 and Wm.det() < 0
assert partial_transpose_B(Wp).det() < 0
assert partial_transpose_B(Wm).det() < 0
rho = rat(4, 5) * psi_m + rat(1, 5) * psi_p
assert (rho * Wm).trace() == rat(7, 80)
assert (rho * Wp).trace() == -rat(3, 80)

print("PASS: ordinary mirror identity and exact PSD spectral decomposition")
print("PASS: extraordinary mirror identity and exact PSD spectral decomposition")
print("PASS: extraordinary partial transpose, exact center and shape equality")
print("PASS: strict-interior rational Class-D counterexample and separating state")
print("Parameter assumptions: ordinary w>=x>=y>=z>0, x+y-w>z;")
print("extraordinary w>=r>q>0 and k>0.")
