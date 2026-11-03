#!/usr/bin/env python3
"""Independent comparison written for this release: brute-force filtering.

For random two-qubit density matrices of ranks 1-4 (some mixed with the
maximally mixed state), maximize F3 of the normalized Alice-filtered state
over all complex 2x2 filters by multistart Nelder-Mead on the eight real
filter parameters, directly on 4x4 matrices, and compare with the closed
spectral formula evaluated from the Bloch data. The formula code below is a
fresh implementation and shares nothing with the other checkers. A
floating-point search can only detect errors; it is not a proof.
"""
import json
from pathlib import Path
import numpy as np
from scipy.optimize import minimize

rng = np.random.default_rng(12345)
P = [np.array([[0, 1], [1, 0]], complex), np.array([[0, -1j], [1j, 0]]),
     np.array([[1, 0], [0, -1]], complex)]
I2 = np.eye(2)


def bloch(r):
    a = np.array([np.trace(r @ np.kron(p, I2)).real for p in P])
    b = np.array([np.trace(r @ np.kron(I2, p)).real for p in P])
    T = np.array([[np.trace(r @ np.kron(p, q)).real for q in P] for p in P])
    return a, b, T


def f3_filtered(r, K):
    KK = np.kron(K, I2)
    s = KK @ r @ KK.conj().T
    s /= np.trace(s).real
    return np.linalg.norm(bloch(s)[2])


def formula(r):
    a, b, T = bloch(r)
    delta = 1 - a @ a
    B = T - np.outer(a, b)
    c = (b - T.T @ a) / delta
    Q = B.T @ (delta * np.eye(3) + np.outer(a, a)) @ B / delta ** 2
    beta, tau = c @ c, np.trace(Q)
    M = np.block([[Q, np.eye(3)], [Q @ np.outer(c, c), Q]])
    # The top root can be a defective double eigenvalue of the nonsymmetric M
    # (the hard case); floating point then splits it into a pair with an
    # imaginary part of order sqrt(machine epsilon), so the tolerance is loose.
    nu = max(e.real for e in np.linalg.eigvals(M) if abs(e.imag) < 1e-6)
    eta = max(tau - beta, nu)
    return np.sqrt(beta + eta + c @ Q @ np.linalg.pinv(eta * np.eye(3) - Q, rcond=1e-12) @ c)


def random_state(rank):
    G = rng.normal(size=(4, rank)) + 1j * rng.normal(size=(4, rank))
    r = G @ G.conj().T
    return r / np.trace(r).real


def brute(r, starts):
    def objective(v):
        K = np.array([[v[0] + 1j * v[1], v[2] + 1j * v[3]], [v[4] + 1j * v[5], v[6] + 1j * v[7]]])
        return -f3_filtered(r, K)
    best = 0.0
    for _ in range(starts):
        res = minimize(objective, rng.normal(size=8), method='Nelder-Mead',
                       options={'maxiter': 6000, 'xatol': 1e-10, 'fatol': 1e-12})
        best = max(best, -res.fun)
    return best


def main():
    rows = []
    for i in range(24):
        rank = 1 + i % 4
        r = random_state(rank)
        if i % 3 == 0:
            r = 0.4 * r + 0.6 * np.eye(4) / 4
        value, search = formula(r), brute(r, 12)
        rows.append({'case': i, 'rank': rank, 'formula': value, 'search': search,
                     'search_minus_formula': search - value})
    excess = max(row['search_minus_formula'] for row in rows)
    shortfall = min(row['search_minus_formula'] for row in rows)
    out = {'cases': len(rows), 'max_search_excess': excess, 'max_search_shortfall': -shortfall,
           'all_passed': bool(excess < 1e-8 and shortfall > -1e-6), 'rows': rows,
           'scope': 'Floating-point multistart search; error detection only, not a proof.'}
    Path(__file__).with_name('independent_bruteforce_results.json').write_text(json.dumps(out, indent=2) + '\n')
    print(json.dumps({k: v for k, v in out.items() if k != 'rows'}, indent=2))
    if not out['all_passed']:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
