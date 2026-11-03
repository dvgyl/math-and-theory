#!/usr/bin/env python3
"""Seeded floating-point falsification searches (NumPy only).

These are attempted counterexample searches, not proofs. Each check reports the
largest violation found; the script exits nonzero if any exceeds TOL.
Run with `python3 -I scripts/check_numeric.py [--quick]`.
"""
import json
import sys

import numpy as np

TOL = 1e-9
rng = np.random.default_rng(20261103)
QUICK = "--quick" in sys.argv
N = 2000 if QUICK else 10000

I2 = np.eye(2)
PAULI = [np.array([[0, 1], [1, 0]], complex), np.array([[0, -1j], [1j, 0]]),
         np.array([[1, 0], [0, -1]], complex)]
report = {}


def bloch(rho):
    a = np.array([np.trace(rho @ np.kron(P, I2)).real for P in PAULI])
    b = np.array([np.trace(rho @ np.kron(I2, P)).real for P in PAULI])
    T = np.array([[np.trace(rho @ np.kron(P, Q)).real for Q in PAULI] for P in PAULI])
    return a, b, T


def chsh_M(T):
    ev = np.sort(np.linalg.eigvalsh(T @ T.T))[::-1]
    return ev[0] + ev[1]


def psd_sqrt(A, inv=False):
    w, V = np.linalg.eigh(A)
    w = np.clip(w, 0, None)
    d = 1 / np.sqrt(w) if inv else np.sqrt(w)
    return (V * d) @ V.conj().T


def wishart(rank):
    G = rng.normal(size=(4, rank)) + 1j * rng.normal(size=(4, rank))
    rho = G @ G.conj().T
    return rho / np.trace(rho).real


def canonical(rho):
    _, b, _ = bloch(rho)
    rhoB = (I2 + sum(b[i] * PAULI[i] for i in range(3))) / 2
    W = np.kron(I2, psd_sqrt(2 * rhoB, inv=True))
    return W @ rho @ W


def bell_value(rho, u, up, v, vp):
    def spin(x):
        return sum(x[i] * PAULI[i] for i in range(3))
    B = np.kron(spin(u), spin(v + vp)) + np.kron(spin(up), spin(v - vp))
    return abs(np.trace(rho @ B))


def filtered(sigma, bvec):
    F = psd_sqrt(I2 + sum(bvec[i] * PAULI[i] for i in range(3)))
    K = np.kron(I2, F)
    return K @ sigma @ K


def unit(n=3):
    x = rng.normal(size=n)
    return x / np.linalg.norm(x)


# 1. Joint bound M <= H(c,r) and shape-gap refinement, random states of all ranks.
worst_H, worst_gap, worst_cov = -np.inf, -np.inf, 0.0
for k in range(N):
    rho = wishart(1 + k % 4)
    a, b, T = bloch(rho)
    r = np.linalg.norm(b)
    sig = canonical(rho)
    ac, bc, C = bloch(sig)
    c = np.linalg.norm(ac)
    cen = (a - T @ b) / (1 - r * r)
    worst_cov = max(worst_cov, np.linalg.norm(cen - ac), np.linalg.norm(bc))
    M = chsh_M(T)
    H = 1 + (1 - r * r) * (1 - 2 * c)
    Dpur = 1 - c + c * c / 2 - np.trace(sig @ sig).real
    worst_H = max(worst_H, M - H)
    worst_gap = max(worst_gap, M - (H - 2 * (1 - r * r) * Dpur))
report["joint_bound_max_excess"] = worst_H
report["shape_gap_max_excess"] = worst_gap
report["whitening_centre_mismatch"] = worst_cov

# Horodecki value cross-check by direct Bell operators on a few states.
worst_direct = 0.0
for k in range(50 if QUICK else 200):
    rho = wishart(1 + k % 4)
    _, _, T = bloch(rho)
    M = chsh_M(T)
    U, sv, Vt = np.linalg.svd(T)
    e1, e2 = Vt[0], Vt[1]
    th = np.arctan2(sv[1], sv[0])
    v, vp = np.cos(th) * e1 + np.sin(th) * e2, np.cos(th) * e1 - np.sin(th) * e2
    u = T @ (v + vp)
    up = T @ (v - vp)
    u = u / np.linalg.norm(u) if np.linalg.norm(u) > 0 else unit()
    up = up / np.linalg.norm(up) if np.linalg.norm(up) > 0 else unit()
    worst_direct = max(worst_direct, abs(bell_value(rho, u, up, v, vp) - 2 * np.sqrt(M)))
    for _ in range(20):  # random settings never exceed 2 sqrt(M)
        worst_direct = max(worst_direct, bell_value(rho, unit(), unit(), unit(), unit()) - 2 * np.sqrt(M))
report["horodecki_direct_mismatch"] = worst_direct


# 2. Equality classification on the filtered obese orbit.
def obese(c):
    w = np.array([1, 0, 0, np.sqrt(1 - c)]) / np.sqrt(2)
    om = np.outer(w, w).astype(complex)
    om[1, 1] += c / 2
    return om


worst_eq, worst_strict = 0.0, np.inf
for _ in range(N // 4):
    c = rng.uniform(0.02, 0.98)
    r = rng.uniform(0.02, 0.98)
    phi = rng.uniform(0, 2 * np.pi)
    w = r * np.sqrt(1 - r * r)
    b_eq = np.array([w * np.cos(phi), w * np.sin(phi), r * r])
    rho = filtered(obese(c), b_eq)
    a, b, T = bloch(rho)
    H = 1 + (1 - r * r) * (1 - 2 * c)
    worst_eq = max(worst_eq, abs(chsh_M(T) - H), abs(np.linalg.norm(b) - r))
    zt = rng.uniform(-r, r)
    if abs(zt - r * r) > 0.05:
        bt = np.array([np.sqrt(r * r - zt * zt), 0, zt])
        _, _, Tt = bloch(filtered(obese(c), bt))
        gap = H - chsh_M(Tt)
        worst_strict = min(worst_strict, gap - c * (1 - c) * (r * r - zt) ** 2)
report["equality_orbit_max_error"] = worst_eq
report["orientation_gap_min_slack"] = worst_strict


# 3. Axial envelope: brute-force maximisation over Bob filter directions.
def axial_sigma(s, t, c):
    return np.array([[1 + c + t, 0, 0, 2 * s], [0, 1 + c - t, 0, 0],
                     [0, 0, 1 - c - t, 0], [2 * s, 0, 0, 1 - c + t]], complex) / 4


def axial_formula(S, T2, c, t, r):
    D = S - T2
    if D > 0 and c * t * r <= D:
        return 2 * S + S * r * r * (c * c / D - 1)
    return S + T2 + 2 * c * t * r + (c * c - S) * r * r


worst_ax, worst_ax_att, count = -np.inf, 0.0, 0
shapes = 100 if QUICK else 300
for _ in range(shapes):
    while True:
        c, t, s = rng.uniform(0, 1), rng.uniform(0, 1), rng.uniform(0, 1)
        if c + t <= 1 and 4 * s * s + c * c <= (1 + t) ** 2:
            break
    sig = axial_sigma(s, t, c)
    assert np.linalg.eigvalsh(sig).min() > -1e-12
    for r in rng.uniform(0, 0.99, size=4):
        f = axial_formula(s * s, t * t, c, t, r)
        zs = np.linspace(-r, r, 801)
        best = -np.inf
        for zz in zs:
            phi = rng.uniform(0, 2 * np.pi)
            rho_t = np.sqrt(max(r * r - zz * zz, 0))
            bb = np.array([rho_t * np.cos(phi), rho_t * np.sin(phi), zz])
            _, _, T = bloch(filtered(sig, bb))
            best = max(best, chsh_M(T))
            count += 1
        worst_ax = max(worst_ax, best - f)
        worst_ax_att = max(worst_ax_att, f - best)
report["axial_max_excess_over_formula"] = worst_ax
report["axial_formula_minus_grid_best"] = worst_ax_att
report["axial_directions_tested"] = count

# 4. Centred triaxial ellipsoids: M_max(r) = l1 + (1 - r^2) l2.
worst_cen, worst_cen_att = -np.inf, 0.0
for _ in range(N // 20):
    while True:
        # canonical centred state with correlation diag(x, y, z) (Pauli-diagonal)
        d = rng.uniform(-1, 1, size=3)
        lam = np.array([1 - d[0] - d[1] - d[2], 1 - d[0] + d[1] + d[2],
                        1 + d[0] - d[1] + d[2], 1 + d[0] + d[1] - d[2]])
        if lam.min() >= 0:
            break
    sig = (np.kron(I2, I2) + sum(d[i] * np.kron(PAULI[i], PAULI[i]) for i in range(3))) / 4
    Ra = np.linalg.qr(rng.normal(size=(2, 2)) + 1j * rng.normal(size=(2, 2)))[0]
    sig = np.kron(Ra, I2) @ sig @ np.kron(Ra, I2).conj().T  # rotate Alice only
    _, _, C = bloch(sig)
    ell = np.sort(np.linalg.eigvalsh(C @ C.T))[::-1]
    r = rng.uniform(0, 0.99)
    f = ell[0] + (1 - r * r) * ell[1]
    best = -np.inf
    for _ in range(60):
        _, _, T = bloch(filtered(sig, r * unit()))
        best = max(best, chsh_M(T))
    worst_cen = max(worst_cen, best - f)
    w, V = np.linalg.eigh(C.T @ C)
    _, _, T = bloch(filtered(sig, r * V[:, -1]))
    worst_cen_att = max(worst_cen_att, abs(chsh_M(T) - f))
report["centred_max_excess_over_formula"] = worst_cen
report["centred_top_direction_error"] = worst_cen_att


# 5. Axial CHSH-breaking criterion against a radius grid of the envelope.
def criterion(S, T2, c, t):
    return 2 * S <= 1 and (S <= c * c + c * t or (1 - S) * (S - c * c) >= S * T2)


mismatch = 0
margin_cases = 0
for _ in range(400 if QUICK else 4000):
    while True:
        c, t, s = rng.uniform(0, 1), rng.uniform(0, 1), rng.uniform(0, 1)
        if c + t <= 1 and 4 * s * s + c * c <= (1 + t) ** 2:
            break
    rs = np.linspace(0, 0.999999, 4001)
    sup = max(axial_formula(s * s, t * t, c, t, rr) for rr in rs)
    pred = criterion(s * s, t * t, c, t)
    if abs(sup - 1) < 1e-4:
        margin_cases += 1
        continue
    if pred != (sup <= 1):
        mismatch += 1
report["channel_criterion_mismatches"] = mismatch
report["channel_criterion_skipped_near_threshold"] = margin_cases

# 6. Sharpness family for the exponent 1/4: distance to random LU images of the
#    obese state never falls below sqrt(p)(sqrt(2-p)-1).
worst_lb = np.inf
for _ in range(200 if QUICK else 1000):
    c = rng.uniform(0.5, 0.999)
    p = 1 - c
    sc = (np.kron(I2, I2) + c * np.kron(PAULI[2], I2) +
          np.sqrt(1 - c * c) * np.kron(PAULI[0], PAULI[2])) / 4
    UA = np.linalg.qr(rng.normal(size=(2, 2)) + 1j * rng.normal(size=(2, 2)))[0]
    UB = np.linalg.qr(rng.normal(size=(2, 2)) + 1j * rng.normal(size=(2, 2)))[0]
    U = np.kron(UA, UB)
    om = U @ obese(c) @ U.conj().T
    dist = np.abs(np.linalg.eigvalsh(sc - om)).sum()
    worst_lb = min(worst_lb, dist - np.sqrt(p) * (np.sqrt(2 - p) - 1))
report["sharpness_lower_bound_min_slack"] = worst_lb

checks = {
    "joint_bound_max_excess": report["joint_bound_max_excess"] <= TOL,
    "shape_gap_max_excess": report["shape_gap_max_excess"] <= TOL,
    "whitening_centre_mismatch": report["whitening_centre_mismatch"] <= 1e-8,
    "horodecki_direct_mismatch": report["horodecki_direct_mismatch"] <= TOL,
    "equality_orbit_max_error": report["equality_orbit_max_error"] <= TOL,
    "orientation_gap_min_slack": report["orientation_gap_min_slack"] >= -TOL,
    "axial_max_excess_over_formula": report["axial_max_excess_over_formula"] <= TOL,
    "axial_formula_minus_grid_best": report["axial_formula_minus_grid_best"] <= 1e-3,
    "centred_max_excess_over_formula": report["centred_max_excess_over_formula"] <= TOL,
    "centred_top_direction_error": report["centred_top_direction_error"] <= TOL,
    "channel_criterion_mismatches": report["channel_criterion_mismatches"] == 0,
    "sharpness_lower_bound_min_slack": report["sharpness_lower_bound_min_slack"] >= -TOL,
}
checks = {k: bool(v) for k, v in checks.items()}
out = {"seed": 20261103, "quick": QUICK, "numpy": np.__version__,
       "all_ok": all(checks.values()), "checks": {k: bool(v) for k, v in checks.items()}, "values": report}
print(json.dumps(out, indent=2, default=float))
sys.exit(0 if out["all_ok"] else 1)
