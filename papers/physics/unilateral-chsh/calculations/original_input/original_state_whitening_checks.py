"""Independent dense-matrix checks of the original-state whitening bridge.

This script does not import the theorem implementation or the optimization code.
It compares the closed coordinates with complex 4x4 operations and an independent
Hermitian eigendecomposition, then checks both directions of arbitrary GL orbits.
"""
from __future__ import annotations

import json
from pathlib import Path

import numpy as np


def main() -> dict:
    rng = np.random.default_rng(240603945)
    identity = np.eye(2, dtype=complex)
    sigma = np.array([
        [[0, 1], [1, 0]],
        [[0, -1j], [1j, 0]],
        [[1, 0], [0, -1]],
    ], dtype=complex)
    left = np.array([np.kron(s, identity) for s in sigma])
    right = np.array([np.kron(identity, s) for s in sigma])
    pairs = np.array([[np.kron(s, t) for t in sigma] for s in sigma])
    worst: dict[str, float] = {}

    def record(name, residual):
        value = float(np.max(np.abs(residual)))
        worst[name] = max(worst.get(name, 0.0), value)
        if not np.isfinite(value) or value > 2e-10:
            raise AssertionError((name, value))

    def coordinates(rho):
        a = np.array([np.trace(rho @ s).real for s in left])
        b = np.array([np.trace(rho @ s).real for s in right])
        t = np.array([[np.trace(rho @ s).real for s in row] for row in pairs])
        return a, b, t

    def state(a, b, t):
        return (np.eye(4) + np.einsum("i,ijk->jk", a, left)
                + np.einsum("i,ijk->jk", b, right)
                + np.einsum("ij,ijkl->kl", t, pairs))/4

    def filter_state(rho, f, normalize=True):
        ff = np.kron(f, identity)
        out = ff @ rho @ ff.conj().T
        return out/np.trace(out) if normalize else out

    min_margin = 1.0
    cases = 0
    for rank in range(1, 5):
        for _ in range(64):
            x = rng.normal(size=(4, rank)) + 1j*rng.normal(size=(4, rank))
            rho = x @ x.conj().T
            rho /= np.trace(rho)
            a, b, t = coordinates(rho)
            record("fano_reconstruction", rho-state(a, b, t))
            marginal = np.trace(rho.reshape(2, 2, 2, 2), axis1=1, axis2=3)
            margin = 1-np.dot(a, a)
            min_margin = min(min_margin, float(margin))
            r = np.sqrt(margin)
            spin_a = np.einsum("i,ijk->jk", a, sigma)
            p_plus = ((1+r)*identity+spin_a)/np.sqrt(2*(1+r))
            p_minus = ((1+r)*identity-spin_a)/np.sqrt(2*(1+r))
            w = p_minus/r
            ev, vectors = np.linalg.eigh(2*marginal)
            w_spectral = (vectors*(1/np.sqrt(ev))) @ vectors.conj().T
            record("explicit_vs_spectral_whitening", w-w_spectral)
            record("left_inverse", w @ p_plus-identity)
            record("right_inverse", p_plus @ w-identity)
            record("marginal_determinant", np.linalg.det(marginal)-margin/4)
            white = filter_state(rho, w, normalize=False)
            c = (b-t.T @ a)/margin
            d = (r*t + np.outer(a, a @ t)/(1+r)-np.outer(a, b))/margin
            record("closed_whitening_state", white-state(np.zeros(3), c, d))
            record("whitened_trace_one", np.trace(white)-1)
            aa, cc, dd = coordinates(white)
            record("whitened_alice_zero", aa)
            record("whitened_bob_formula", cc-c)
            record("whitened_correlation_formula", dd-d)
            f = rng.normal(size=(2, 2)) + 1j*rng.normal(size=(2, 2))
            g = rng.normal(size=(2, 2)) + 1j*rng.normal(size=(2, 2))
            assert abs(np.linalg.det(f)) > 1e-14 and abs(np.linalg.det(g)) > 1e-14
            record("original_to_canonical_orbit",
                   filter_state(rho, f)-filter_state(white, f @ p_plus))
            record("canonical_to_original_orbit",
                   filter_state(white, g)-filter_state(rho, g @ w))
            cases += 1
    result = {
        "status": "PASS",
        "seed": 240603945,
        "cases": cases,
        "input_ranks": [1, 2, 3, 4],
        "independent_complex_GL_comparisons": 2*cases,
        "minimum_bloch_margin": min_margin,
        "absolute_tolerance": 2e-10,
        "maximum_residuals": worst,
    }
    Path(__file__).with_name("original_state_whitening_results.json").write_text(
        json.dumps(result, indent=2)+"\n")
    return result


if __name__ == "__main__":
    print(json.dumps(main(), indent=2))
