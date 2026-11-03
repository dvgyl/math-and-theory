#!/usr/bin/env python3
"""Reproduce numerical checks for the exact one-sided F3 theorem.

Run: python verify_one_sided.py --samples 100 --output one_sided_checks.json
Dependencies: NumPy and SciPy.  Numerical checks complement the mathematical
and Lean proofs; they are not substituted for those proofs.
"""
import argparse
import json
from fractions import Fraction as F
from pathlib import Path
import numpy as np
from scipy.optimize import brentq, minimize
from verify_geometry import bloch, whiten_bob


def trust_region_maximum(tau, k, K):
    values, vectors = np.linalg.eigh(K)
    coordinates = vectors.T @ k
    tol = 1e-10
    if values[0] > tol:
        stationary = coordinates / values
        if stationary @ stationary <= 1:
            x = vectors @ stationary
            return tau + k @ x, x, 0.0
    lower = max(0.0, -values[0])
    shifted = values + lower
    zero = np.abs(shifted) < tol
    particular = np.zeros(3)
    particular[~zero] = coordinates[~zero] / shifted[~zero]
    if np.linalg.norm(coordinates[zero]) < tol and particular @ particular <= 1:
        if lower > 0:
            particular[np.flatnonzero(zero)[0]] = np.sqrt(max(0, 1-particular@particular))
        x = vectors @ particular
        return tau + 2*k@x - x@K@x, x, lower

    def equation(lam):
        y = coordinates/(values+lam)
        return float(y@y - 1)
    lo = np.nextafter(lower, np.inf)
    if not np.isfinite(equation(lo)):
        lo = lower + 1e-15
    hi = max(1.0, lower+1)
    while equation(hi) > 0:
        hi = 2*hi+1
    lam = brentq(equation, lo, hi, xtol=1e-14)
    x = vectors @ (coordinates/(values+lam))
    return tau + 2*k@x-x@K@x, x, lam


def rational_counterexample():
    c, t, sx, sy = F(3,10), F(3,5), F(3,10), -F(1,5)
    tau = sx*sx+sy*sy+t*t
    K = [tau-c*c-s*s for s in (sx,sy,t)]
    kz = t*c
    r = kz/K[2]
    value = tau+kz*r
    boundary = tau+2*kz-K[2]
    assert K == [F(31,100),F(9,25),F(1,25)]
    assert r == F(9,2) and value == F(13,10) and boundary == F(81,100)
    assert 19*13-5**2 > 0 and 7*1-1**2 > 0
    return {
        "matrix_numerator": [[19,0,0,5],[0,7,1,0],[0,1,1,0],[5,0,0,13]],
        "matrix_denominator": 40,
        "positive_block_determinants_before_scaling": [222,6],
        "center": str(c),
        "correlation_diagonal": [str(sx),str(sy),str(t)],
        "tau": str(tau),
        "K_diagonal": [str(x) for x in K],
        "stationary_radius": str(r),
        "unconstrained_value": str(value),
        "actual_orbit_supremum": str(boundary),
    }


def run(samples):
    rng = np.random.default_rng(9031126)
    result = {
        "seed":9031126,
        "samples":samples,
        "rational_counterexample":rational_counterexample(),
        "criterion_disagreements":0,
        "violating_orbits":0,
        "max_SLSQP_vs_exact_difference":0.0,
        "max_geometric_formula_difference":0.0,
        "max_primal_dual_difference":0.0,
        "max_candidate_radius_violation":0.0,
        "max_stationary_branch_value_error":0.0,
    }
    for j in range(samples):
        rank = 1+j%4
        g = rng.normal(size=(4,rank))+1j*rng.normal(size=(4,rank))
        rho = g@g.conj().T
        rho /= np.trace(rho)
        sigma = whiten_bob(rho)
        c, _, S = bloch(sigma)
        tau = np.sum(S*S)
        K = (tau-c@c)*np.eye(3)-S.T@S
        k = S.T@c
        value, candidate, lam = trust_region_maximum(tau,k,K)
        criterion = False
        if np.linalg.eigvalsh(K)[0] > 1e-10:
            stationary = np.linalg.solve(K,k)
            V = tau+k@stationary
            criterion = stationary@stationary < 1-1e-9 and V > 1+1e-9
            if criterion:
                result["max_stationary_branch_value_error"] = max(
                    result["max_stationary_branch_value_error"],float(abs(V-value)))
            L = (tau-c@c)*np.eye(3)-S@S.T
            li_c = np.linalg.solve(L,c)
            Vq = tau + c@(S@S.T)@li_c
            r2q = li_c@(S@S.T)@li_c
            result["max_geometric_formula_difference"] = max(
                result["max_geometric_formula_difference"],
                float(abs(Vq-V)),float(abs(r2q-stationary@stationary)))
        if abs(value-1) > 1e-8 and criterion != (value > 1):
            result["criterion_disagreements"] += 1
        result["violating_orbits"] += int(value > 1+1e-8)
        result["max_candidate_radius_violation"] = max(
            result["max_candidate_radius_violation"],float(max(0,candidate@candidate-1)))
        dual = tau+lam+k@np.linalg.pinv(K+lam*np.eye(3))@k
        result["max_primal_dual_difference"] = max(
            result["max_primal_dual_difference"],float(abs(dual-value)))

        def objective(x):
            return -(tau+2*k@x-x@K@x)
        def gradient(x):
            return 2*K@x-2*k
        starts = [np.zeros(3)]
        for _ in range(3):
            x = rng.normal(size=3)
            starts.append(x/np.linalg.norm(x)*0.8)
        found = []
        for start in starts:
            opt = minimize(objective,start,jac=gradient,method="SLSQP",
                constraints={"type":"ineq","fun":lambda x:1-x@x,"jac":lambda x:-2*x},
                options={"ftol":1e-12,"maxiter":300})
            if opt.success:
                found.append(-opt.fun)
        if not found:
            raise RuntimeError("All independent constrained optimizations failed")
        result["max_SLSQP_vs_exact_difference"] = max(
            result["max_SLSQP_vs_exact_difference"],float(abs(max(found)-value)))
    result["all_checks_passed"] = (
        result["criterion_disagreements"] == 0
        and all(v < 1e-7 for k,v in result.items() if k.startswith("max_"))
    )
    return result


if __name__ == "__main__":
    p = argparse.ArgumentParser()
    p.add_argument("--samples",type=int,default=100)
    p.add_argument("--output",type=Path)
    args = p.parse_args()
    report = run(args.samples)
    text = json.dumps(report,indent=2)+"\n"
    if args.output:
        args.output.write_text(text)
    print(text,end="")
    raise SystemExit(0 if report["all_checks_passed"] else 1)
