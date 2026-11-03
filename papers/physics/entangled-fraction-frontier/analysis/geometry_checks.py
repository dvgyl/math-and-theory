#!/usr/bin/env python3
"""Exact and numerical independent checks for the signed-ellipsoid FEF envelope.

Requires Python >=3.10, numpy, sympy. No network access or input files.
Numerical tests are checks for counterexamples, not proofs.
"""
import json
from pathlib import Path

import numpy as np
import sympy as sp


def symbolic_checks():
    c = sp.symbols("c1:4", real=True)
    t = sp.symbols("t1:4", real=True)
    z = sp.Symbol("z")
    eye = sp.eye(2)
    pauli = [sp.Matrix([[0, 1], [1, 0]]),
             sp.Matrix([[0, -sp.I], [sp.I, 0]]), sp.diag(1, -1)]
    H = sum((c[i] * sp.kronecker_product(pauli[i], eye)
             + t[i] * sp.kronecker_product(pauli[i], pauli[i])
             for i in range(3)), sp.zeros(4))
    cs = sum(x*x for x in c)
    q = sum(x*x for x in t)
    q2 = sum(x**4 for x in t)
    k = sum(c[i]**2*t[i]**2 for i in range(3))
    d = sp.prod(t)
    r = cs + q
    poly = z**4 - 2*r*z**2 + 8*d*z + r*r - 4*k - 2*q*q + 2*q2
    outcomes = {
        "characteristic_polynomial": sp.expand(H.charpoly(z).as_expr()-poly) == 0,
        "trace_H_squared": sp.expand(sp.trace(H**2)-4*r) == 0,
        "trace_H_cubed": sp.expand(sp.trace(H**3)+24*d) == 0,
        "trace_H_fourth": sp.expand(sp.trace(H**4)-4*r*r-16*k-8*(q*q-q2)) == 0,
    }
    sigma = sp.Matrix([[sp.Rational(9,20),0,0,sp.Rational(1,5)],
                       [0,sp.Rational(7,20),0,0],
                       [0,0,sp.Rational(1,20),0],
                       [sp.Rational(1,5),0,0,sp.Rational(3,20)]])
    F = sp.diag(1, sp.Rational(1,2))
    K = sp.kronecker_product(eye, F)
    p = sp.trace(K*sigma*K.H)
    rho = K*sigma*K.H/p
    phi = sp.Matrix([1,0,0,1])/sp.sqrt(2)
    outcomes.update({
        "example_spectrum": sigma.eigenvals() == {
            sp.Rational(11,20):1,sp.Rational(7,20):1,sp.Rational(1,20):2},
        "example_success": p == sp.Rational(5,8),
        "example_Bell_overlap": (phi.H*rho*phi)[0] == sp.Rational(11,20),
        "example_expected_output": rho == sp.Matrix([
            [sp.Rational(18,25),0,0,sp.Rational(4,25)],
            [0,sp.Rational(7,50),0,0],
            [0,0,sp.Rational(2,25),0],
            [sp.Rational(4,25),0,0,sp.Rational(3,50)]])
    })
    assert all(outcomes.values()), outcomes
    return outcomes


P = np.array([[[0,1],[1,0]], [[0,-1j],[1j,0]], [[1,0],[0,-1]]])
I = np.eye(2)


def marginal_B(rho):
    return np.trace(rho.reshape(2,2,2,2), axis1=0, axis2=2)


def bloch(rho):
    c = np.array([np.trace(rho@np.kron(p,I)).real for p in P])
    T = np.array([[np.trace(rho@np.kron(p,q)).real for q in P] for p in P])
    return c,T


def fef(rho):
    _,T = bloch(rho)
    s = np.linalg.svd(T,compute_uv=False)
    return (1+s[0]+s[1]-np.sign(np.linalg.det(T))*s[2])/4


def numerical_checks(n=2000,seed=20261103):
    rng = np.random.default_rng(seed)
    maximum_poly_residual = 0.
    maximum_attainment_error = 0.
    maximum_bound_violation = 0.
    maximum_center_bound_violation = 0.
    maximum_marginal_error = 0.
    for i in range(n):
        # All ranks are sampled, including rank-one and rank-deficient states.
        rank = 1 + i % 4
        G = rng.normal(size=(4,rank))+1j*rng.normal(size=(4,rank))
        rho = G@G.conj().T
        rho /= np.trace(rho)
        vals,U = np.linalg.eigh(marginal_B(rho))
        W = U@np.diag(1/np.sqrt(2*vals))@U.conj().T
        L = np.kron(I,W)
        sigma = L@rho@L.conj().T
        maximum_marginal_error = max(maximum_marginal_error,
                                    np.linalg.norm(marginal_B(sigma)-I/2))
        c,T = bloch(sigma)
        Q = T@T.T
        r = c@c+np.trace(Q)
        k = c@Q@c
        q = np.trace(Q)
        q2 = np.trace(Q@Q)
        d = np.linalg.det(T)
        eig,V = np.linalg.eigh(sigma)
        z = 4*eig-1
        resid = z**4-2*r*z*z+8*d*z+r*r-4*k-2*q*q+2*q2
        maximum_poly_residual = max(maximum_poly_residual,max(abs(resid)))
        top = eig[-1]
        vector = V[:,-1]
        F = np.sqrt(2)*vector.reshape(2,2).conj()
        F /= np.linalg.norm(F,ord=2)
        M = np.kron(I,F)
        output = M@sigma@M.conj().T
        output /= np.trace(output)
        maximum_attainment_error=max(maximum_attainment_error,abs(fef(output)-top))
        maximum_bound_violation=max(maximum_bound_violation,fef(rho)-top)
        maximum_center_bound_violation=max(maximum_center_bound_violation,
                                           top-(1-np.linalg.norm(c)/2))
    out = dict(seed=seed,samples=n,rank_counts={str(k):n//4 for k in range(1,5)},
               maximum_poly_residual=maximum_poly_residual,
               maximum_attainment_error=maximum_attainment_error,
               maximum_bound_violation=maximum_bound_violation,
               maximum_center_bound_violation=maximum_center_bound_violation,
               maximum_marginal_error=maximum_marginal_error)
    assert maximum_poly_residual < 1e-9,out
    assert maximum_attainment_error < 1e-10,out
    assert maximum_bound_violation < 1e-10,out
    assert maximum_center_bound_violation < 1e-10,out
    return out


if __name__ == "__main__":
    result = {"exact":symbolic_checks(),"numerical":numerical_checks()}
    text = json.dumps(result,indent=2)
    print(text)
    Path(__file__).with_name("geometry_check_results.json").write_text(text+"\n")
