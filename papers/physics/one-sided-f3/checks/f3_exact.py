"""Exact spectral prescription for one-sided filtered F3, evaluated in float64.

The theorem is algebraic.  This implementation is a numerical evaluator, not a
substitute for its proof or an exact-arithmetic certificate.  No optimization
routine is used here.  See verify.py for independent direct filtering checks.
"""
from dataclasses import dataclass
import numpy as np
from numpy.linalg import eigh, eigvals, norm

PAULI = np.array([[[0, 1], [1, 0]], [[0, -1j], [1j, 0]],
                  [[1, 0], [0, -1]]], dtype=complex)
I2 = np.eye(2, dtype=complex)


def bloch(rho):
    a = np.array([np.trace(rho @ np.kron(s, I2)).real for s in PAULI])
    b = np.array([np.trace(rho @ np.kron(I2, s)).real for s in PAULI])
    T = np.array([[np.trace(rho @ np.kron(s, t)).real for t in PAULI]
                  for s in PAULI])
    return a, b, T


def density(a, b, T):
    rho = np.kron(I2, I2)
    for i in range(3):
        rho = rho + a[i] * np.kron(PAULI[i], I2)
        rho = rho + b[i] * np.kron(I2, PAULI[i])
        for j in range(3):
            rho = rho + T[i, j] * np.kron(PAULI[i], PAULI[j])
    return rho / 4


def positive_sqrt(A):
    w, U = eigh((A + A.conj().T) / 2)
    return (U * np.sqrt(np.maximum(w, 0))) @ U.conj().T


def inv_positive_sqrt(A):
    w, U = eigh((A + A.conj().T) / 2)
    if min(w) <= 0:
        raise ValueError('Inverse square root requires a positive definite matrix')
    return (U * (1 / np.sqrt(w))) @ U.conj().T


def canonical(a, b, T):
    delta = 1 - a @ a
    if delta <= 0:
        raise ValueError('Pure marginal must use the separate theorem branch')
    L = np.sqrt(delta) * np.eye(3) + np.outer(a, a) / (1 + np.sqrt(delta))
    c = (b - T.T @ a) / delta
    S = (L @ T - np.outer(a, b)) / delta
    B = T - np.outer(a, b)
    Q = B.T @ (delta * np.eye(3) + np.outer(a, a)) @ B / delta**2
    return c, S, (Q + Q.T) / 2


@dataclass
class QuadraticSolution:
    value: float
    multiplier: float
    x: np.ndarray
    x0: np.ndarray
    H: np.ndarray
    g: np.ndarray
    branch: str
    residual: float


def quadratic_spectral(tau, H, g, tol=2e-11):
    """Maximize tau + x.H.x + 2g.x on the unit ball by finite spectra.

    The exact prescription is lambda=max(0,max_real_eigenvalue(M)).
    Explicit interior/hard-case classification avoids spurious roundoff at
    repeated eigenvalues of M.  All tolerances are numerical implementation
    tolerances, not part of the theorem.
    """
    H = (H + H.T) / 2
    h, U = eigh(H)
    w = U.T @ g
    scale = max(1., norm(H), norm(g))
    eps = tol * scale
    posD = -h > eps
    p = np.zeros(3)
    p[posD] = w[posD] / (-h[posD])
    if max(h) <= eps and norm(w[~posD]) <= eps and p @ p <= 1 + tol:
        lam = 0.
        x0 = U @ p
        x = x0.copy()
        branch = 'interior' if norm(x0) < 1 - tol else 'boundary-zero-multiplier'
    else:
        top = h[-1]
        topmask = np.abs(h - top) <= eps
        p = np.zeros(3)
        p[~topmask] = w[~topmask] / (top - h[~topmask])
        if top > 0 and norm(w[topmask]) <= eps and p @ p <= 1 + tol:
            lam = float(top)
            x0 = U @ p
            x = x0 + np.sqrt(max(0., 1 - x0 @ x0)) * U[:, np.flatnonzero(topmask)[0]]
            branch = 'hard'
        else:
            M = np.block([[H, np.eye(3)], [np.outer(g, g), H]])
            ev = eigvals(M)
            real = ev.real[np.abs(ev.imag) <= 1e-7 * scale]
            if len(real) == 0:
                raise ArithmeticError('No numerically real eigenvalue; increase precision')
            lam = max(0., float(max(real)))
            p = w / (lam - h)
            x0 = U @ p
            x = x0.copy()
            branch = 'regular-boundary'
    D = lam * np.eye(3) - H
    value = float(tau + lam + g @ x0)
    residual = max(norm(D @ x - g), abs(lam * (1 - x @ x)),
                   max(0., norm(x) - 1), max(0., -min(eigh(D)[0])),
                   abs(value - (tau + x @ H @ x + 2 * g @ x)))
    return QuadraticSolution(value, lam, x, x0, H, g, branch, float(residual))


def one_sided(a, b, T, side='A', tol=2e-11):
    if side == 'B':
        a, b, T = b, a, T.T
    elif side != 'A':
        raise ValueError("side must be 'A' or 'B'")
    delta = 1 - a @ a
    if delta == 0:
        # Never collapse a nearly pure entangled marginal into this branch.
        # Even arbitrarily weak pure-state entanglement can be filtered to Bell.
        if not np.array_equal(T, np.outer(a, b)):
            raise ArithmeticError('Marginal rounded to pure while correlations remain; '
                                  'use exact or higher-precision arithmetic')
        return {'F3': float(norm(b)), 'F3_squared': float(b @ b),
                'branch': 'pure-marginal', 'attained_invertibly': True,
                'filter': I2.copy(), 'solution': None}
    if delta <= tol:
        raise ArithmeticError('Marginal is too close to pure for this float64 evaluator; '
                              'use exact or higher-precision arithmetic')
    c, S, Q = canonical(a, b, T)
    tau = float(np.trace(Q))
    H = S @ S.T + (c @ c - tau) * np.eye(3)
    g = S @ c
    sol = quadratic_spectral(tau, H, g, tol=tol)
    W = inv_positive_sqrt(I2 + np.einsum('i,ijk->jk', a, PAULI))
    effect = I2 + np.einsum('i,ijk->jk', sol.x, PAULI)
    K = positive_sqrt(effect) @ W
    K /= norm(K, 2)  # makes K^* K <= I, without changing the state
    d = tau - c @ c
    HQ = Q - d * np.eye(3)
    Mq = np.block([[HQ, np.eye(3)], [Q @ np.outer(c, c), HQ]])
    return {'F3': float(np.sqrt(max(0., sol.value))), 'F3_squared': sol.value,
            'branch': sol.branch,
            'attained_invertibly': sol.multiplier == 0 and norm(sol.x0) < 1 - tol,
            'filter': K, 'solution': sol, 'c': c, 'S': S, 'Q': Q,
            'shape_spectral_matrix': Mq}


def apply_filter(rho, K, side='A'):
    op = np.kron(K, I2) if side == 'A' else np.kron(I2, K)
    r = op @ rho @ op.conj().T
    probability = np.trace(r).real
    if probability <= 0:
        raise ValueError('Zero success probability')
    return r / probability, float(probability)


def original_fraction(a, b, T, x):
    t = float(np.sum(T * T))
    H = T @ T.T + (b @ b - t) * np.eye(3)
    return float((t + 2 * x @ T @ b + x @ H @ x) / (1 + a @ x)**2)
