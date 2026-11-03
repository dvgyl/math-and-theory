#!/usr/bin/env python3
"""Reproduce exact algebra and matrix checks for the V2 geometry/probability results.
These checks supplement, and do not replace, the written and Lean proofs.
Run: python verify_probability_geometry.py
"""
import json
from pathlib import Path
import numpy as np
import sympy as sp

I2 = np.eye(2, dtype=complex)
PAULI = np.array([[[0, 1], [1, 0]], [[0, -1j], [1j, 0]], [[1, 0], [0, -1]]])
ATOL = 4e-11
rng = np.random.default_rng(240603945)


def H(c, r):
    return (1-r*r)*(3-4*c)+(c+(1-c)*r)**2


def radial_optimum(c, p):
    R = (1-p)/p
    return min(R, c*(1-c)/(2-2*c-c*c)) if c <= 2/3 else R


def corr(rho):
    return np.array([[np.trace(rho @ np.kron(x, y)).real for y in PAULI] for x in PAULI])


def bloch(rho):
    a = np.array([np.trace(rho @ np.kron(x, I2)).real for x in PAULI])
    b = np.array([np.trace(rho @ np.kron(I2, x)).real for x in PAULI])
    return a, b, corr(rho)


def positive_sqrt(E):
    lam, U = np.linalg.eigh(E)
    assert np.min(lam) >= -ATOL
    return (U * np.sqrt(np.maximum(lam, 0))) @ U.conj().T


def apply(rho, G):
    L = np.kron(I2, G)
    unnormalized = L @ rho @ L.conj().T
    probability = np.trace(unnormalized).real
    return probability, unnormalized/probability


def obese(c):
    psi = np.array([0, 1, np.sqrt(1-c), 0], dtype=complex)
    rho = np.outer(psi, psi.conj())/2
    rho[0, 0] += c/2
    return rho


def interval_state(c, t, alpha):
    a, b, e, d = (1+c+t)/4, (1+c-t)/4, (1-c-t)/4, (1-c+t)/4
    rho = np.diag([a, b, e, d]).astype(complex)
    rho[0, 3] = rho[3, 0] = alpha*np.sqrt(max(0, a*d))
    rho[1, 2] = rho[2, 1] = alpha*np.sqrt(max(0, b*e))
    return rho


def canonical_random_state():
    X = rng.normal(size=(4, 4))+1j*rng.normal(size=(4, 4))
    rho = X @ X.conj().T
    rho /= np.trace(rho)
    B = np.einsum('abad->bd', rho.reshape(2, 2, 2, 2))
    lam, U = np.linalg.eigh(B)
    invsqrt = (U / np.sqrt(2*lam)) @ U.conj().T
    L = np.kron(I2, invsqrt)
    sigma = L @ rho @ L.conj().T
    assert abs(np.trace(sigma)-1) < ATOL
    return sigma


def main():
    c, r, p = sp.symbols('c r p', real=True)
    D = 2-2*c-c*c
    h = (1-r*r)*(3-4*c)+(c+(1-c)*r)**2
    g = 2-2*(1+p)*c+(2*p-1)*c*c
    exact_checks = {
        'quadratic_expansion': sp.expand(h-(3-4*c+c*c+2*c*(1-c)*r-D*r*r)) == 0,
        'activation_factorization': sp.expand(h-1-(1-r)*(D*r+2-4*c+c*c)) == 0,
        'probability_endpoint_identity': sp.factor((h-1).subs(r, (1-p)/p)-(2*p-1)*g/p**2) == 0,
        'nonbinding_cutoff': sp.factor(1/(1+c*(1-c)/D)-D/(2-c-2*c*c)) == 0,
    }
    assert all(exact_checks.values())
    interval_count = 0
    rank_checks = 0
    for cc in [0, .1, .5, 2/3, .9, 1]:
        for fraction in [0, .2, .7, 1]:
            tt = fraction*(1-cc)
            for alpha in [0, .2, .6, 1]:
                rho = interval_state(cc, tt, alpha)
                assert np.linalg.eigvalsh(rho).min() >= -ATOL
                a, b, T = bloch(rho)
                assert np.linalg.norm(a-np.array([0, 0, cc])) < ATOL
                assert np.linalg.norm(b) < ATOL
                assert abs(np.linalg.norm(T[2, :])-tt) < ATOL
                assert abs(np.sum(T*T)-(tt*tt+alpha*alpha*(1-cc*cc+tt*tt))) < ATOL
                if alpha == 1:
                    target = np.sort([0, 0, (1-tt)/2, (1+tt)/2])
                    assert np.max(np.abs(np.linalg.eigvalsh(rho)-target)) < ATOL
                    rank_checks += 1
                interval_count += 1
    volume_witness_count = 0
    for cc in [0, .1, .5, 2/3, .9, 1]:
        for fraction in [0, .2, .7, 1]:
            tt = fraction*(1-cc)
            aa, bb, ee, dd = (1+cc+tt)/4, (1+cc-tt)/4, (1-cc-tt)/4, (1-cc+tt)/4
            U, V = aa*dd, bb*ee
            for lam in [0, .1, .5, .9, 1]:
                ss = lam*(U+V)
                W, J = (ss, 0) if ss <= U else (U, ss-U)
                rho = np.diag([aa, bb, ee, dd]).astype(complex)
                rho[0, 3] = rho[3, 0] = np.sqrt(max(0, W))
                rho[1, 2] = rho[2, 1] = np.sqrt(max(0, J))
                assert np.linalg.eigvalsh(rho).min() >= -ATOL
                T = corr(rho)
                tau = np.sum(T*T)
                cap = tt/2*min(tau-tt*tt, 1+2*tt+2*tt*tt-cc*cc-tau)
                assert abs(abs(np.linalg.det(T))-cap) < ATOL
                volume_witness_count += 1
    probability_count = 0
    for cc in [0, .1, .5, 2-sp.sqrt(2).evalf(), 2/3, .9, 1]:
        cc = float(cc)
        for pp in [.5, .6, .75, .9, 1]:
            rr = radial_optimum(cc, pp)
            G = np.sqrt(pp)*np.diag([np.sqrt(1-rr), np.sqrt(1+rr)])
            assert np.linalg.eigvalsh(I2-G.conj().T@G).min() >= -ATOL
            prob, out = apply(obese(cc), G)
            assert abs(prob-pp) < ATOL
            assert abs(np.sum(corr(out)**2)-H(cc, rr)) < ATOL
            radius_grid = np.linspace(0, (1-pp)/pp, 3001)
            assert np.max(H(cc, radius_grid)) <= H(cc, rr)+ATOL
            ccrit = 2/(1+pp+np.sqrt((1-pp)**2+2))
            if abs(cc-ccrit) > 1e-9:
                assert (H(cc, rr) > 1+1e-10) == (cc < ccrit)
            probability_count += 1
    random_count = 300
    max_bound_error = 0.0
    max_probability_error = 0.0
    for _ in range(random_count):
        sigma = canonical_random_state()
        a, b, T = bloch(sigma)
        assert np.linalg.norm(b) < ATOL
        cc = np.linalg.norm(a)
        nn = a/cc if cc > 1e-12 else np.array([0., 0., 1.])
        tt = np.linalg.norm(T.T@nn)
        tau = np.sum(T*T)
        signed_lower = -tt*((1+tt)**2-cc*cc)/4
        signed_upper = tt*((1-tt)**2-cc*cc)/4
        detT = np.linalg.det(T)
        cubic = 16*np.trace(sigma@sigma@sigma).real
        assert abs(cubic-(1+3*cc*cc+3*tau-6*detT)) < ATOL
        cap = tt/2*min(tau-tt*tt, 1+2*tt+2*tt*tt-cc*cc-tau)
        assert signed_lower-ATOL <= detT <= signed_upper+ATOL
        assert abs(detT) <= cap+ATOL
        v = rng.normal(size=3)
        v /= np.linalg.norm(v)
        rr = rng.uniform(0, 1)
        F = positive_sqrt(I2+rr*np.einsum('i,ijk->jk', v, PAULI))
        Z = rng.normal(size=(2, 2))+1j*rng.normal(size=(2, 2))
        U, _ = np.linalg.qr(Z)
        pp = rng.uniform(.01, 1)/(1+rr)
        G = np.sqrt(pp)*U@F
        prob, out = apply(sigma, G)
        value = np.sum(corr(out)**2)
        max_probability_error = max(max_probability_error, abs(prob-pp))
        max_bound_error = max(max_bound_error, value-H(cc, rr))
        assert abs(prob-pp) < ATOL
        assert value <= H(cc, rr)+ATOL
        assert np.linalg.eigvalsh(I2-G.conj().T@G).min() >= -ATOL
    p_singular, out_singular = apply(obese(.8), np.diag([0., 1.]))
    a, b, T = bloch(out_singular)
    assert abs(p_singular-.5) < ATOL
    assert abs(np.linalg.norm(a)-1) < ATOL and abs(np.linalg.norm(b)-1) < ATOL
    assert abs(np.sum(T*T)-1) < ATOL
    result = {
        'seed': 240603945, 'exact_symbolic_checks': exact_checks,
        'physical_interval_states_checked': interval_count,
        'sharp_spectra_checked': rank_checks,
        'sharp_triple_volume_witnesses': volume_witness_count,
        'sharp_probability_grid_points': probability_count,
        'random_complex_Kraus_operations': random_count,
        'canonical_cubic_trace_identity_checks': random_count,
        'maximum_random_upper_bound_violation': max_bound_error,
        'maximum_actual_success_probability_error': max_probability_error,
        'singular_endpoint': {'input_center': .8, 'success': p_singular,
            'output_center': float(np.linalg.norm(a)), 'F3_squared': float(np.sum(T*T))},
        'status': 'all checks passed; numerical checks are not proofs',
    }
    output = Path(__file__).with_name('probability_geometry_checks.json')
    output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
