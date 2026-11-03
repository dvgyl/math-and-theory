#!/usr/bin/env python3
"""Independent deterministic numerical checks; these are not proofs.

Requires Python 3 and NumPy.  Run from any directory:
    python verify_geometry.py --samples 2000 --output geometry_checks.json

The accompanying proof note establishes the exact statements.  This script
checks Pauli conventions, rank-deficient examples, sharp witnesses, the full
matrix inequality, and the explicit trace-norm rigidity bound.
"""
import argparse
import json
from pathlib import Path
import numpy as np

I = np.eye(2, dtype=complex)
X = np.array([[0, 1], [1, 0]], dtype=complex)
Y = np.array([[0, -1j], [1j, 0]], dtype=complex)
Z = np.diag([1.0, -1.0]).astype(complex)
P = (X, Y, Z)
PA = np.array([np.kron(p, I) for p in P])
PB = np.array([np.kron(I, p) for p in P])
PT = np.array([[np.kron(p, q) for q in P] for p in P])
SPIN = np.kron(Y, Y)


def bloch(rho):
    a = np.einsum("ij,kji->k", rho, PA).real
    b = np.einsum("ij,kji->k", rho, PB).real
    T = np.einsum("ij,klji->kl", rho, PT).real
    return a, b, T


def pauli(v):
    return sum(v[i] * P[i] for i in range(3))


def conjugate(rho, ua, ub):
    u = np.kron(ua, ub)
    return u @ rho @ u.conj().T


def align_unitary(v):
    """Return U carrying v.sigma to |v| Z by conjugation."""
    if np.linalg.norm(v) < 1e-13:
        return I
    _, eigvectors = np.linalg.eigh(pauli(v))
    return eigvectors[:, ::-1].conj().T


def whiten_bob(rho):
    _, b, _ = bloch(rho)
    values, vectors = np.linalg.eigh(I + pauli(b))
    if values[0] <= 1e-12:
        raise ValueError("Singular Bob marginal: whitening is undefined.")
    f = (vectors * (values ** -0.5)) @ vectors.conj().T
    out = conjugate(rho, I, f)
    # The mathematical trace is exactly one; no data-dependent normalization.
    return out


def align_canonical(sigma):
    cvec, _, _ = bloch(sigma)
    ua = align_unitary(cvec)
    aligned = conjugate(sigma, ua, I)
    cvec, _, S = bloch(aligned)
    ub = align_unitary(S[2, :])
    aligned = conjugate(aligned, I, ub)
    theta = np.angle(aligned[0, 3])
    phase = np.diag([np.exp(-0.5j * theta), np.exp(0.5j * theta)])
    return conjugate(aligned, phase, I)


def witness(c, t):
    ap, am = (1 + c + t) / 4, (1 + c - t) / 4
    dp, dm = (1 - c + t) / 4, (1 - c - t) / 4
    w, v = np.sqrt(max(0, ap * dp)), np.sqrt(max(0, am * dm))
    return np.array(
        [[ap, 0, 0, w], [0, am, v, 0], [0, v, dm, 0], [w, 0, 0, dp]],
        dtype=complex,
    )


def global_envelope(c):
    if c >= 2 / 3:
        return 1.0
    return 1 + (2 - 3 * c) ** 2 / (2 - 2 * c - c * c)


def run(samples):
    rng = np.random.default_rng(20261103)
    out = {
        "seed": 20261103,
        "samples": samples,
        "global_ranks_tested": [1, 2, 3, 4],
        "numerical_checks_are_not_proofs": True,
        "max_spinflip_identity_error": 0.0,
        "min_matrix_inequality_eigenvalue": 10.0,
        "max_whitening_marginal_error": 0.0,
        "max_canonical_form_error": 0.0,
        "min_radial_bound_slack": 10.0,
        "min_global_envelope_slack": 10.0,
        "min_canonical_stability_slack": 10.0,
        "min_adaptive_stability_slack": 10.0,
        "max_filter_identity_error": 0.0,
        "max_fixed_width_witness_error": 0.0,
        "max_global_witness_error": 0.0,
    }
    for sample in range(samples):
        rank = 1 + sample % 4
        g = rng.normal(size=(4, rank)) + 1j * rng.normal(size=(4, rank))
        rho = g @ g.conj().T
        rho /= np.trace(rho)
        a, b, T = bloch(rho)
        tau = np.sum(T * T)
        ma = (1 + a @ a - b @ b - tau) * np.eye(3) + 2 * (
            T @ T.T - np.outer(a, a)
        )
        mb = (1 + b @ b - a @ a - tau) * np.eye(3) + 2 * (
            T.T @ T - np.outer(b, b)
        )
        out["min_matrix_inequality_eigenvalue"] = min(
            out["min_matrix_inequality_eigenvalue"],
            float(np.linalg.eigvalsh(ma).min()),
            float(np.linalg.eigvalsh(mb).min()),
        )
        n = rng.normal(size=3)
        n /= np.linalg.norm(n)
        unitary = np.kron(pauli(n), I) @ SPIN
        reflected = unitary @ rho.conj() @ unitary.conj().T
        error = abs(4 * np.trace(rho @ reflected).real - n @ ma @ n)
        out["max_spinflip_identity_error"] = max(
            out["max_spinflip_identity_error"], float(error)
        )
        canonical = whiten_bob(rho)
        cv, cb, S = bloch(canonical)
        c, r = np.linalg.norm(cv), np.linalg.norm(b)
        out["max_whitening_marginal_error"] = max(
            out["max_whitening_marginal_error"],
            float(np.linalg.norm(cb)),
            float(abs(np.trace(canonical) - 1)),
        )
        error = abs(tau - ((1 - r * r) * (np.sum(S * S) - c * c) + a @ a))
        out["max_filter_identity_error"] = max(
            out["max_filter_identity_error"], float(error)
        )
        out["min_global_envelope_slack"] = min(
            out["min_global_envelope_slack"], float(global_envelope(c) - tau)
        )
        aligned = align_canonical(canonical)
        cv, _, S = bloch(aligned)
        # Tiny roundoff in the Bell-state case is harmless and is recorded above.
        c = max(0.0, float(cv[2]))
        t = max(0.0, float(S[2, 2]))
        z, w, v = aligned[0, 2], aligned[0, 3], aligned[1, 2]
        expected = np.array(
            [
                [(1+c+t)/4, 0, z, w],
                [0, (1+c-t)/4, v, -z],
                [z.conjugate(), v.conjugate(), (1-c-t)/4, 0],
                [w.conjugate(), -z.conjugate(), 0, (1-c+t)/4],
            ], dtype=complex,
        )
        out["max_canonical_form_error"] = max(
            out["max_canonical_form_error"], float(np.max(np.abs(aligned - expected)))
        )
        d = 1 - c
        trq = float(np.sum(S * S))
        delta = d * (3 - c) - trq
        radial_slack = 1 - c*c + 2*t*t - trq
        out["min_radial_bound_slack"] = min(
            out["min_radial_bound_slack"], float(radial_slack)
        )
        if d > 1e-10:
            obese = witness(c, d)
            trace_norm = np.sum(np.abs(np.linalg.eigvalsh(aligned - obese)))
            stability_slack = (5+c)/(2*d) * delta - trace_norm**2
            out["min_canonical_stability_slack"] = min(
                out["min_canonical_stability_slack"], float(stability_slack)
            )
            adaptive_slack = (0.5 + (2+c)/(d+t)) * delta - trace_norm**2
            out["min_adaptive_stability_slack"] = min(
                out["min_adaptive_stability_slack"], float(adaptive_slack)
            )
    for c in (0.0, 0.1, 0.5, 2/3, 0.9, 1.0):
        for t in np.linspace(0, 1-c, 7):
            sigma = witness(c, t)
            a, b, S = bloch(sigma)
            target_eigs = np.array([0, 0, (1-t)/2, (1+t)/2])
            errors = [
                np.max(np.abs(a - [0,0,c])),
                np.linalg.norm(b),
                abs(np.sum(S*S) - (1-c*c+2*t*t)),
                abs(np.linalg.det(S) + t*t),
                np.max(np.abs(np.linalg.eigvalsh(sigma) - target_eigs)),
            ]
            out["max_fixed_width_witness_error"] = max(
                out["max_fixed_width_witness_error"], float(max(errors))
            )
    for c in (0.0, 0.1, 0.25, 0.5, 0.6, 0.65):
        d, D = 1-c, 2-2*c-c*c
        r = c*d/D
        f = np.diag([np.sqrt(1+r), np.sqrt(1-r)])
        rho = conjugate(witness(c,d), I, f)
        a, b, T = bloch(rho)
        center = (a - T @ b)/(1-b@b)
        error = max(
            abs(np.sum(T*T)-global_envelope(c)),
            abs(np.linalg.norm(center)-c),
            abs(np.linalg.norm(b)-r),
            abs(np.trace(rho)-1),
        )
        out["max_global_witness_error"] = max(
            out["max_global_witness_error"], float(error)
        )
    tolerance = 1e-8
    out["all_checks_passed"] = all(
        value >= -tolerance if key.startswith("min_") else value <= tolerance
        for key, value in out.items()
        if key.startswith("min_") or key.startswith("max_")
    )
    return out


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--samples", type=int, default=2000)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = run(args.samples)
    rendered = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.write_text(rendered)
    print(rendered, end="")
    raise SystemExit(0 if result["all_checks_passed"] else 1)
