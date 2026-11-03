#!/usr/bin/env python3
"""Exact symbolic checks for the CHSH steering-centre package (SymPy).

Every identity is checked by simplification to zero or by exact evaluation.
Run with `python3 -I scripts/check_exact.py`; it prints a JSON report and exits
nonzero on the first failure.
"""
import json
import sys

import sympy as sp

I2 = sp.eye(2)
PAULI = [sp.Matrix([[0, 1], [1, 0]]), sp.Matrix([[0, -sp.I], [sp.I, 0]]),
         sp.Matrix([[1, 0], [0, -1]])]
results = {}


def record(name, ok, **extra):
    results[name] = dict(ok=bool(ok), **extra)
    if not ok:
        print(json.dumps(results, indent=2, default=str))
        sys.exit(f"FAILED: {name}")


def kron(a, b):
    return sp.kronecker_product(a, b)


def bloch(rho):
    a = [sp.simplify((rho * kron(P, I2)).trace()) for P in PAULI]
    b = [sp.simplify((rho * kron(I2, P)).trace()) for P in PAULI]
    T = sp.Matrix(3, 3, lambda i, j: sp.simplify((rho * kron(PAULI[i], PAULI[j])).trace()))
    return sp.Matrix(a), sp.Matrix(b), T


def is_zero(expr):
    return sp.simplify(sp.expand(expr)) == 0


def zero_matrix(m):
    return all(is_zero(x) for x in m)


# 1. The dyadic joint-envelope extremizer (the Lean family `CHSHPhysical.state`).
c, r = sp.symbols('c r', nonnegative=True)
p = 1 - c
s = sp.sqrt(1 - r**2)
a = sp.sqrt(p) * s
v0 = sp.Matrix([(1 + r) / 2, -(1 - r) / 2, a / 2, a / 2])
v1 = sp.sqrt(c) * s / 2 * sp.Matrix([1, 1, 0, 0])
rho = v0 * v0.T + v1 * v1.T
av, bv, T = bloch(rho)
h = p + c * r**2
q = p * (1 - r**2)
x = sp.symbols('x')
charpoly = (x * sp.eye(3) - T * T.T).det()
centre = (av - T * bv) / (1 - r**2)
record("family_trace_one", is_zero(rho.trace() - 1))
record("family_bob_vector", zero_matrix(bv - sp.Matrix([0, 0, r])))
record("family_alice_vector", zero_matrix(av - sp.Matrix([r * a, 0, c + p * r**2])))
record("family_correlation_matrix",
       zero_matrix(T - sp.Matrix([[r * a, 0, a], [0, -a, 0], [-p * (1 - r**2), 0, r]])))
record("family_centre", zero_matrix(centre - sp.Matrix([0, 0, c])))
record("family_gram_charpoly", is_zero(charpoly - (x - h) * (x - q) * (x - q * h)))
record("family_M_equals_H", is_zero(h + q - (1 + (1 - r**2) * (1 - 2 * c))))
record("family_spectral_order", True,
       note="h - q = r^2 >= 0 and q - qh = q(1-h) = q c (1-r^2) >= 0")
assert is_zero(h - q - r**2) and is_zero(q - q * h - q * c * (1 - r**2))

# 2. Gram block of a filtered maximally obese state (joint-envelope proof).
u = sp.symbols('u', nonnegative=True)
z = sp.symbols('z', real=True)
R = u + z**2
k = (1 - 2 * c) * (1 - R)
hh = 1 + k - q.subs(r**2, R)
qq = p * (1 - R)
B = sp.Matrix([[p * (1 - z**2), sp.sqrt(p * u) * (c + p * z)],
               [sp.sqrt(p * u) * (c + p * z), k + (c + p * z)**2]])
record("joint_interlacing_det", is_zero((qq * I2 - B).det() + c * p * u * (1 - R)))
G = hh * I2 - B
record("joint_gap_11", is_zero(G[0, 0] - (c * u + z**2)))
record("joint_gap_22", is_zero(G[1, 1] - p * (u + c * (z - 1)**2)))
record("joint_gap_det", is_zero(G.det() - c * p * (R - z)**2))
record("joint_h_value", is_zero(hh - (p + c * R)))

# The block is the actual Gram matrix TT^T of the filtered obese state.
cv = sp.Matrix([0, 0, c])
C = sp.diag(sp.sqrt(p), -sp.sqrt(p), p)
bvec = sp.Matrix([sp.sqrt(u), 0, z])
avec = cv + C * bvec
gram = avec * avec.T + (1 - R) * (C * C.T - cv * cv.T)
record("joint_block_is_gram",
       zero_matrix(sp.Matrix([[gram[0, 0], gram[0, 2]], [gram[2, 0], gram[2, 2]]]) - B)
       and is_zero(gram[1, 1] - qq) and is_zero(gram[0, 1]) and is_zero(gram[1, 2]))

# Gram formula from an explicit whitening, checked on the obese state with a
# generic filter F_b = sqrt(I + b.sigma) (rational point to keep SymPy exact).
cval, bx, bz = sp.Rational(1, 3), sp.Rational(1, 3), sp.Rational(1, 4)
pv = 1 - cval
w = sp.Matrix([1, 0, 0, sp.sqrt(pv)]) / sp.sqrt(2)
omega = w * w.T + cval / 2 * sp.Matrix(4, 4, lambda i, j: 1 if i == j == 1 else 0)
bb = sp.Matrix([bx, 0, bz])
rb = sp.sqrt(bx**2 + bz**2)
alpha = (sp.sqrt(1 + rb) + sp.sqrt(1 - rb)) / 2
gamma = 1 / (sp.sqrt(1 + rb) + sp.sqrt(1 - rb))
F = alpha * I2 + gamma * (bx * PAULI[0] + bz * PAULI[2])
record("filter_square", zero_matrix(sp.simplify(F * F - (I2 + bx * PAULI[0] + bz * PAULI[2]))))
rho_f = kron(I2, F) * omega * kron(I2, F)
a_f, b_f, T_f = bloch(rho_f)
C0 = sp.diag(sp.sqrt(pv), -sp.sqrt(pv), pv)
c0 = sp.Matrix([0, 0, cval])
record("filtered_trace_and_bob", is_zero(rho_f.trace() - 1) and zero_matrix(b_f - bb))
record("filtered_centre", zero_matrix(sp.simplify((a_f - T_f * b_f) / (1 - rb**2) - c0)))
record("filtered_gram_formula",
       zero_matrix(sp.simplify(T_f * T_f.T - (a_f * a_f.T + (1 - rb**2) * (C0 * C0.T - c0 * c0.T)))))

# 3. Axial ellipsoid identities.
S_, t, cc, Rr, zz = sp.symbols('S t c R z', real=True)
ss = sp.sqrt(S_)
Tt = t**2
D = S_ - Tt
qa = S_ * (1 - Rr)
Ba = sp.Matrix([[S_ * (1 - zz**2), ss * sp.sqrt(Rr - zz**2) * (cc + t * zz)],
                [ss * sp.sqrt(Rr - zz**2) * (cc + t * zz), (1 - Rr) * (Tt - cc**2) + (cc + t * zz)**2]])
record("axial_interlacing_det",
       is_zero((qa * I2 - Ba).det() + S_ * (Rr - zz**2) * (1 - Rr) * (D + cc**2)))
hi = S_ + S_ * cc**2 * Rr / D
zi = cc * t * Rr / D
Gi = hi * I2 - Ba
record("axial_interior_gap_11", is_zero(sp.together(Gi[0, 0] - (S_ * zz**2 + S_ * cc**2 * Rr / D))))
record("axial_interior_gap_det", is_zero(sp.together(Gi.det() - S_ * (D + cc**2) * (zz - zi)**2)))
rr = sp.symbols('rr', real=True)  # Bob length, R = rr^2
Bb = Ba.subs(Rr, rr**2)
qb = S_ * (1 - rr**2)
hb = (t + cc * rr)**2
Ab = hb * D + qb * cc**2
Lb = (cc + rr * t) * (t + cc * rr) * (cc * t * rr - D)
Gb = hb * I2 - Bb
record("axial_boundary_gap_11", is_zero(Gb[0, 0] - (-D + 2 * cc * t * rr + cc**2 * rr**2 + S_ * zz**2)))
record("axial_boundary_gap_det", is_zero(Gb.det() - (Ab * (rr - zz)**2 + 2 * Lb * (rr - zz))))
record("axial_boundary_endpoint",
       is_zero(Ab * rr - cc * t * (hb - qb) - (cc + rr * t) * (t + cc * rr) * (D - cc * t * rr)))
record("axial_prolate_trace",
       is_zero(qb + (t + cc * rr)**2 - Bb.trace() - (rr - zz) * ((Tt - S_) * (rr + zz) + 2 * cc * t)))
record("axial_branches_agree",
       is_zero((2 * S_ + S_ * rr**2 * (cc**2 / D - 1) - (S_ + Tt + 2 * cc * t * rr + (cc**2 - S_) * rr**2))
               .subs(rr, D / (cc * t))))

# 4. The tilted nonspherical witness (c = 1/5, Q = diag(3/5,3/5,9/25), r = 1/2).
s5 = sp.sqrt(5)
W = sp.Matrix([[81, -9 * s5, 45, 15 * s5], [-9 * s5, 21, -9 * s5, -15],
               [45, -9 * s5, 39, 9 * s5], [15 * s5, -15, 9 * s5, 19]]) / 160
Lw = sp.Matrix([[1, 0, 0, 0], [-s5 / 9, 1, 0, 0], [sp.Rational(5, 9), -s5 / 4, 1, 0],
                [5 * s5 / 27, -sp.Rational(5, 12), -s5 / 9, 1]])
Dw = sp.diag(sp.Rational(81, 160), sp.Rational(1, 10), sp.Rational(9, 160), sp.Rational(1, 90))
record("witness_ldl", zero_matrix(sp.simplify(Lw * Dw * Lw.T - W)))
aw, bw, Tw = bloch(W)
record("witness_trace", W.trace() == 1)
record("witness_bloch", zero_matrix(aw - sp.Matrix([sp.Rational(3, 8), 0, sp.Rational(11, 40)]))
       and zero_matrix(bw - sp.Matrix([0, 0, sp.Rational(1, 2)])))
record("witness_centre", zero_matrix(sp.simplify((aw - Tw * bw) / (1 - sp.Rational(1, 4))
                                                  - sp.Matrix([0, 0, sp.Rational(1, 5)]))))
# Whitening: sigma = (I x (2 rho_B)^{-1/2}) rho (I x (2 rho_B)^{-1/2}).
rhoB = sp.diag(sp.Rational(3, 4), sp.Rational(1, 4))
Wh = sp.diag(1 / sp.sqrt(2 * rhoB[0, 0]), 1 / sp.sqrt(2 * rhoB[1, 1]))
sig = kron(I2, Wh) * W * kron(I2, Wh)
_, bsig, Csig = bloch(sig)
Qw = sp.simplify(Csig * Csig.T)
record("witness_shape", zero_matrix(bsig) and
       sorted(sp.Poly((x * sp.eye(3) - Qw).det(), x).all_roots()) ==
       sorted([sp.Rational(9, 25), sp.Rational(3, 5), sp.Rational(3, 5)]))
TtT = sp.simplify(Tw.T * Tw)
record("witness_TtT", zero_matrix(TtT - sp.diag(sp.Rational(9, 32), sp.Rational(9, 20), sp.Rational(5, 8))))


def spin(vec):
    return sum((vec[i] * PAULI[i] for i in range(3)), sp.zeros(2))


al = sp.Matrix([3, 0, 1]) / sp.sqrt(10)
alp = sp.Matrix([0, -1, 0])
be = sp.Matrix([0, sp.sqrt(18), 5]) / sp.sqrt(43)
bep = sp.Matrix([0, -sp.sqrt(18), 5]) / sp.sqrt(43)
bell = kron(spin(al), spin(be + bep)) + kron(spin(alp), spin(be - bep))
val = sp.nsimplify(sp.simplify((W * bell).trace()))
record("witness_bell_value", is_zero(val - 2 * sp.sqrt(sp.Rational(43, 40))), value=str(val))
record("witness_M", sp.Rational(9, 20) + sp.Rational(5, 8) == sp.Rational(43, 40))
# Aligned filter at the same radius: axial formula boundary branch value.
Sv, tv, cv5, rv = sp.Rational(3, 5), sp.Rational(3, 5), sp.Rational(1, 5), sp.Rational(1, 2)
aligned = Sv + tv**2 + 2 * cv5 * tv * rv + (cv5**2 - Sv) * rv**2
interior = 2 * Sv + Sv * rv**2 * (cv5**2 / (Sv - tv**2) - 1)
record("witness_aligned_vs_tilted", aligned == sp.Rational(47, 50) and interior == sp.Rational(43, 40)
       and cv5 * tv * rv <= Sv - tv**2)

# 5. Rank-two separable sharpness family for the exponent 1/4.
cs = sp.symbols('c', positive=True)
sig_c = (kron(I2, I2) + cs * kron(PAULI[2], I2) + sp.sqrt(1 - cs**2) * kron(PAULI[0], PAULI[2])) / 4
record("sharpness_projection", zero_matrix(sp.simplify(sig_c * sig_c - sig_c / 2)))
record("sharpness_canonical", zero_matrix(bloch(sig_c)[1]))
purity = sp.simplify((sig_c * sig_c).trace())
Dpur = 1 - cs + cs**2 / 2 - purity
record("sharpness_deficit", is_zero(Dpur - (1 - cs)**2 / 2))
Tc = bloch(sig_c)[2]
gram_c = sp.simplify(Tc * Tc.T)
record("sharpness_M", gram_c.rank() == 1 and is_zero(gram_c.trace() - (1 - cs**2))
       and is_zero(2 * (1 - cs) - gram_c.trace() - (1 - cs)**2))
# Every LU image of the obese state has correlation operator norm sqrt(1-c).
pp = sp.symbols('p', positive=True)
ratio = (sp.sqrt(2 * pp - pp**2) - sp.sqrt(pp)) / (pp**2 / 2)**sp.Rational(1, 4)
record("sharpness_lower_bound_limit",
       is_zero(sp.powsimp(sp.simplify(ratio - 2**sp.Rational(1, 4) * (sp.sqrt(2 - pp) - 1)), force=True))
       and sp.limit(2**sp.Rational(1, 4) * (sp.sqrt(2 - pp) - 1), pp, 0) == 2**sp.Rational(1, 4) * (sp.sqrt(2) - 1))

# 6. Countercertificate to the printed optimizer in Zhang et al. (2020), App. B.
Tz = sp.Matrix([[sp.sqrt(6) / 16, 0, -3 * sp.sqrt(5) / 16], [0, -sp.sqrt(6) / 4, 0],
                [sp.sqrt(30) / 8, 0, sp.Rational(3, 8)]])
ev = (Tz * Tz.T).eigenvals(multiple=True)
evn = sorted(ev, key=lambda e: float(e), reverse=True)
Mz = sp.nsimplify(sp.simplify(evn[0] + evn[1]))
record("printed_direction_value", is_zero(Mz - (399 + 9 * sp.sqrt(145)) / 512), value=str(Mz))
record("printed_direction_strict", 113**2 - 81 * 145 == 1024 and float(Mz) < 1)

# 7. Exact noncanonical equality state at c = 1/2, r = 1/2.
s6 = sp.sqrt(6)
rs = sp.Matrix([[21, -3, 3 * s6, 3 * s6], [-3, 5, -s6, -s6], [3 * s6, -s6, 3, 3], [3 * s6, -s6, 3, 3]]) / 32
w0 = sp.Matrix([sp.Rational(3, 4), -sp.Rational(1, 4), s6 / 8, s6 / 8])
w1 = sp.Matrix([s6 / 8, s6 / 8, 0, 0])
ar, br, Tr = bloch(rs)
record("equality_state_dyadic", zero_matrix(sp.simplify(w0 * w0.T + w1 * w1.T - rs)))
record("equality_state_centre",
       zero_matrix(sp.simplify((ar - Tr * br) / (1 - br.dot(br)) - sp.Matrix([0, 0, sp.Rational(1, 2)]))))
evr = sorted((Tr * Tr.T).eigenvals(multiple=True), key=lambda e: float(e), reverse=True)
record("equality_state_M", is_zero(evr[0] + evr[1] - 1))

# 8. Translated sphere: canonical state is not optimal (s = 2/3, c = 1/3).
s5b = sp.sqrt(5)
rsph = sp.Matrix([[15, 0, 0, 2 * s5b], [0, 1, 0, 0], [0, 0, 0, 0], [2 * s5b, 0, 0, 2]]) / 18
asph, bsph, Tsph = bloch(rsph)
evs = sorted((Tsph * Tsph.T).eigenvals(multiple=True), key=lambda e: float(e), reverse=True)
record("sphere_example", is_zero(evs[0] + evs[1] - sp.Rational(28, 27)) and
       zero_matrix(sp.simplify((asph - Tsph * bsph) / (1 - bsph.dot(bsph)) - sp.Matrix([0, 0, sp.Rational(1, 3)]))))

print(json.dumps({"checks": len(results), "all_ok": all(v["ok"] for v in results.values()),
                  "results": results}, indent=2, default=str))
