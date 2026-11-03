#!/usr/bin/env python3
"""Independent numerical and exact-polynomial audit of centre/F3 bounds.

Run: python independent_audit.py --samples 4096
Only numpy and sympy are required. Floating-point experiments are cross-checks,
not the proof. The polynomial identities are exact SymPy identities.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

import numpy as np
import sympy as sp

PAULI = np.array([
    [[0, 1], [1, 0]],
    [[0, -1j], [1j, 0]],
    [[1, 0], [0, -1]],
], dtype=complex)
I2 = np.eye(2)


def partial_a(rho):
    return np.einsum('abcb->ac', rho.reshape(2, 2, 2, 2))


def partial_b(rho):
    return np.einsum('abad->bd', rho.reshape(2, 2, 2, 2))


def bloch(rho):
    return np.array([np.trace(rho @ s).real for s in PAULI])


def parameters(rho):
    a = bloch(partial_a(rho))
    b = bloch(partial_b(rho))
    T = np.array([[np.trace(rho @ np.kron(s, t)).real
                   for t in PAULI] for s in PAULI])
    return a, b, T


def canonicalize(rho):
    eig, U = np.linalg.eigh(2 * partial_b(rho))
    if eig.min() <= 1e-12:
        raise ValueError('rank-deficient marginal: use the product branch')
    F = (U * np.sqrt(eig)) @ U.conj().T
    Fi = (U * (1 / np.sqrt(eig))) @ U.conj().T
    K = np.kron(I2, Fi)
    return K @ rho @ K, F


def envelope(c):
    return 1 + (2 - 3*c)**2 / (2 - 2*c - c*c) if c < 2/3 else 1.


def purity_difference(M):
    return np.trace(M @ M) - np.trace(partial_a(M) @ partial_a(M))


def sharp_skew_state(c, t):
    """Canonical PSD rank <=2 witness for 0<=t<=1-c.

    It has centre c e_z, q=t^2, and tr Q = 1-c^2+2t^2.
    The representation as two outer products proves PSD independently of eigensolvers.
    """
    u = np.array([np.sqrt(max(0, 1+c+t)), 0, 0,
                  np.sqrt(max(0, 1-c+t))], dtype=complex) / 2
    v = np.array([0, np.sqrt(max(0, 1+c-t)),
                  np.sqrt(max(0, 1-c-t)), 0], dtype=complex) / 2
    return np.outer(u, u.conj()) + np.outer(v, v.conj())


def obese_filtered(c, r):
    v = np.array([0, np.sqrt(1+r), np.sqrt((1-c)*(1-r)), 0])
    rho = np.outer(v, v)/2
    rho[0, 0] += c*(1-r)/2
    return rho.astype(complex)


def symbolic_checks():
    c, r, p, q, m, z = sp.symbols('c r p q m z', real=True)
    D = 2 - 2*c - c*c
    Q = (1-r*r)*(3-4*c) + (c+(1-c)*r)**2
    square = D+(2-3*c)**2-D*Q-(D*r-c*(1-c))**2
    flat = 1-Q-(1-r)**2*(4*c-2-c*c)-r*(1-r)*(6*c-4)
    # y has norm squared m and n.y=z; cvec=c*n and a=(1-r)cvec+r*y.
    anorm2 = (1-r)**2*c*c+r*r*m+2*r*(1-r)*c*z
    R = (1-r*r)*(p-c*c)+anorm2
    G = 1+(2-3*c)**2/D
    tau = 1-c*c+2*q-p
    rhs = ((D*r-c*(1-c))**2/D
           +(1-r*r)*(2*((1-c)**2-q)+tau)
           +r*(r+c*(1-r))*(1-m)
           +r*c*(1-r)*(m+1-2*z))
    exact = {
        'interior_completed_square': sp.factor(square) == 0,
        'flat_branch_deficit': sp.factor(flat) == 0,
        'geometric_deficit_decomposition': sp.factor(G-R-rhs) == 0,
    }
    A = sp.Matrix(2, 2, sp.symbols('a:4'))
    B = sp.Matrix(2, 2, sp.symbols('b:4'))
    F = sp.Matrix(2, 2, sp.symbols('f:4'))
    J = lambda X, Y: sp.trace(X*Y)-sp.trace(X)*sp.trace(Y)
    exact['complex_block_filter_covariance'] = (
        sp.expand(J(F*A*F, F*B*F)-F.det()**2*J(A, B)) == 0)
    assert all(exact.values())
    return exact


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--samples', type=int, default=4096)
    parser.add_argument('--seed', type=int, default=240603945)
    parser.add_argument('--output', type=Path, default=Path(__file__).with_name('independent_audit.json'))
    args = parser.parse_args()
    rng = np.random.default_rng(args.seed)
    minima = {k: float('inf') for k in [
        'canonical_spectral_slack', 'canonical_purity_slack',
        'global_envelope_slack', 'radial_support_slack',
        'skew_trace_slack', 'geometry_matrix_min_eigenvalue',
        'general_matrix_min_eigenvalue']}
    errors = {k: 0. for k in [
        'centre_formula', 'purity_covariance', 'correlation_identity',
        'spin_flip_overlap_identity', 'geometric_deficit_identity',
        'sharp_skew_state_trace', 'sharp_skew_state_marginal',
        'sharp_skew_state_equality', 'interior_optimizer_value',
        'singular_product_value']}
    def err(k, v):
        errors[k] = max(errors[k], float(abs(v)))
    def slack(k, v):
        minima[k] = min(minima[k], float(v))
    ranks = {str(k): 0 for k in range(1, 5)}
    for index in range(args.samples):
        rank = 1+index % 4
        ranks[str(rank)] += 1
        X = rng.normal(size=(4, rank))+1j*rng.normal(size=(4, rank))
        rho = X@X.conj().T
        rho /= np.trace(rho)
        a, b, T = parameters(rho)
        sigma, F = canonicalize(rho)
        cv, _, S = parameters(sigma)
        c, r = np.linalg.norm(cv), np.linalg.norm(b)
        Q = S@S.T
        p = np.trace(Q)
        n = cv/c if c > 1e-10 else np.array([0., 0., 1.])
        q = n@Q@n
        tau = 1-c*c+2*q-p
        R = np.linalg.norm(T)**2
        gmatrix = 2*(Q-np.outer(cv, cv))+(1+c*c-p)*np.eye(3)
        hmatrix = (2*(T@T.T-np.outer(a, a))
                   +(1+a@a-b@b-R)*np.eye(3))
        slack('canonical_spectral_slack', 1-c/2-np.linalg.eigvalsh(sigma).max())
        slack('canonical_purity_slack', 1-c+c*c/2-np.trace(sigma@sigma).real)
        slack('global_envelope_slack', envelope(c)-R)
        slack('radial_support_slack', (1-c)**2-q)
        slack('skew_trace_slack', tau)
        slack('geometry_matrix_min_eigenvalue', np.linalg.eigvalsh(gmatrix).min())
        slack('general_matrix_min_eigenvalue', np.linalg.eigvalsh(hmatrix).min())
        err('centre_formula', np.linalg.norm(cv-(a-T@b)/(1-b@b)))
        err('purity_covariance', purity_difference(rho)-np.linalg.det(F)**2*purity_difference(sigma))
        err('correlation_identity', R-(1-r*r)*(p-c*c)-a@a)
        U = np.kron(np.einsum('i,ijk->jk', n, PAULI)@PAULI[1], PAULI[1])
        flipped = U@sigma.T@U.conj().T
        # If c=0 the directional formula still uses cv exactly.
        exact_trace = 1+c*c-2*(cv@n)**2+2*q-p
        err('spin_flip_overlap_identity', exact_trace-4*np.trace(sigma@flipped))
        if c > 1e-10 and c < 2/3 and r > 1e-10:
            y = cv+S@(b/r)
            D = 2-2*c-c*c
            rp = c*(1-c)/D
            rhs = (D*(r-rp)**2+(1-r*r)*(2*((1-c)**2-q)+tau)
                   +r*(r+c*(1-r))*(1-y@y)
                   +r*c*(1-r)*np.linalg.norm(y-n)**2)
            err('geometric_deficit_identity', envelope(c)-R-rhs)
    for c in np.linspace(0., 1., 41):
        for t in np.linspace(0., 1-c, 23):
            sigma = sharp_skew_state(c, t)
            cv, b, S = parameters(sigma)
            err('sharp_skew_state_trace', np.trace(sigma)-1)
            err('sharp_skew_state_marginal', np.linalg.norm(b))
            err('sharp_skew_state_equality', np.linalg.norm(S)**2-(1-c*c+2*t*t))
            assert np.linalg.eigvalsh(sigma).min() >= -1e-12
        # Singular marginal is a product, using the point-ellipsoid convention.
        product = np.kron(np.diag([(1+c)/2, (1-c)/2]), np.diag([1., 0.]))
        a, b, T = parameters(product)
        err('singular_product_value', np.linalg.norm(T)**2-c*c)
    for c in np.linspace(0., 2/3-1e-4, 101):
        r = c*(1-c)/(2-2*c-c*c)
        rho = obese_filtered(c, r)
        err('interior_optimizer_value', np.linalg.norm(parameters(rho)[2])**2-envelope(c))
    result = {'seed': args.seed, 'samples': args.samples, 'rank_counts': ranks,
              'exact_symbolic_checks': symbolic_checks(),
              'minimum_slacks': minima, 'maximum_identity_errors': errors,
              'scope': 'Independent exact polynomial and floating-point cross-checks; not a substitute for the proof.'}
    # Whitening rank-one states near singular marginals may amplify rounding.
    result['passed'] = all(v > -1e-8 for v in minima.values()) and all(v < 1e-7 for v in errors.values())
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))
    if not result['passed']:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
