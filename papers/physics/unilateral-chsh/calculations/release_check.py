"""Release check written for this package, independent of the uploaded solvers.

It recomputes, from explicit 4x4 density matrices and without importing any
other file of the package:

1. exact (SymPy) values: the guard-region formula tr A - lambda_min(A + C K^-1 C)
   for the rank-three example rho_1 (79/75), the full-rank example rho_2
   (Alice value 32/25), and the quasi-distillable family
   p*singlet + (1-p)|00><00| on a grid of rational p, where the squared
   unilateral optimum is max(1, 2p/(2-p)); the explicit optimal filter of
   rho_1 is applied to the density matrix and its Horodecki value recomputed;
2. numerical: for random density matrices of ranks one to four with
   alpha > 1 on Alice's side, the Schur value against (a) the value of the
   reconstructed invertible filter applied to the original density matrix
   and (b) a multistart direct maximization over invertible filters.

Usage: python3 release_check.py [--output release_check.json]
The checks corroborate the proofs; no theorem rests on them.
"""
from pathlib import Path
import argparse
import json

import numpy as np
from scipy.optimize import minimize
import sympy as sp

PAULI = [np.array([[0, 1], [1, 0]], complex), np.array([[0, -1j], [1j, 0]]),
         np.array([[1, 0], [0, -1]], complex)]
SP_PAULI = [sp.Matrix([[0, 1], [1, 0]]), sp.Matrix([[0, -sp.I], [sp.I, 0]]),
            sp.Matrix([[1, 0], [0, -1]])]


def sp_bloch(rho):
    """Exact Bloch data (a, b, T) of a SymPy 4x4 matrix."""
    one = sp.eye(2)
    tr = lambda m: sp.nsimplify(sp.simplify((rho * m).trace()))
    a = [tr(sp.kronecker_product(s, one)) for s in SP_PAULI]
    b = [tr(sp.kronecker_product(one, s)) for s in SP_PAULI]
    T = [[tr(sp.kronecker_product(s, t)) for t in SP_PAULI] for s in SP_PAULI]
    return a, b, T


def canonical_data_exact(a, b, T):
    """Whitened Bloch data (c, D) of the Alice-whitened state, exact formulas."""
    a, b, T = sp.Matrix(a), sp.Matrix(b), sp.Matrix(T)
    h = 1 - (a.T * a)[0]
    r = sp.sqrt(h)
    c = (b - T.T * a) / h
    D = ((r * sp.eye(3) + a * a.T / (1 + r)) * T - a * b.T) / h
    return sp.simplify(c), sp.simplify(D)


def schur_value_exact(c, D):
    A = D * D.T
    s = (c.T * c)[0]
    d = D * c
    C = sp.Matrix([[0, -d[2], d[1]], [d[2], 0, -d[0]], [-d[1], d[0], 0]])
    K = A - s * sp.eye(3)
    alpha = sp.simplify(A.trace() - s)
    M = sp.simplify(A + C * K.inv() * C)
    lam = sp.symbols('lam')
    roots = sp.Poly(sp.factor((M - lam * sp.eye(3)).det()), lam).all_roots()
    lmin = min(roots, key=lambda z: float(sp.re(sp.N(z, 50))))
    return sp.nsimplify(sp.simplify(A.trace() - lmin)), alpha


def horodecki_sq(T):
    sv = np.linalg.svd(np.asarray(T, float), compute_uv=False)
    return float(sv[0] ** 2 + sv[1] ** 2)


def np_bloch(rho):
    I = np.eye(2)
    a = np.array([np.trace(rho @ np.kron(s, I)).real for s in PAULI])
    b = np.array([np.trace(rho @ np.kron(I, s)).real for s in PAULI])
    T = np.array([[np.trace(rho @ np.kron(s, t)).real for t in PAULI] for s in PAULI])
    return a, b, T


def filtered_value(rho, F):
    G = np.kron(F, np.eye(2))
    out = G @ rho @ G.conj().T
    out = out / np.trace(out).real
    return horodecki_sq(np_bloch(out)[2])


def sqrtm_psd(X):
    w, V = np.linalg.eigh(X)
    return (V * np.sqrt(np.clip(w, 0, None))) @ V.conj().T


def schur_numeric(rho):
    """Guard-region value, alpha, and the reconstructed filter on the original state."""
    a, b, T = np_bloch(rho)
    rhoA = (np.eye(2) + sum(a[i] * PAULI[i] for i in range(3))) / 2
    W = np.linalg.inv(sqrtm_psd(2 * rhoA))
    G = np.kron(W, np.eye(2))
    canon = G @ rho @ G.conj().T
    _, c, D = np_bloch(canon)
    A = D @ D.T
    s = c @ c
    d = D @ c
    C = np.array([[0, -d[2], d[1]], [d[2], 0, -d[0]], [-d[1], d[0], 0]])
    K = A - s * np.eye(3)
    alpha = np.trace(A) - s
    M = A + C @ np.linalg.solve(K, C)
    w, V = np.linalg.eigh((M + M.T) / 2)
    n = V[:, 0]
    v = -np.linalg.solve(K, C @ n)
    u = -np.cross(n, v)
    effect = np.eye(2) + sum(u[i] * PAULI[i] for i in range(3))
    F = sqrtm_psd(effect) @ W
    return float(np.trace(A) - w[0]), float(alpha), F, float(np.linalg.norm(v))


def random_state(rng, rank):
    X = rng.normal(size=(4, rank)) + 1j * rng.normal(size=(4, rank))
    rho = X @ X.conj().T
    return rho / np.trace(rho).real


def direct_max(rho, rng, starts=12):
    best = -1.0
    for _ in range(starts):
        x0 = rng.normal(size=8)

        def neg(x):
            F = np.array([[x[0] + 1j * x[1], x[2] + 1j * x[3]], [x[4] + 1j * x[5], x[6] + 1j * x[7]]])
            if abs(np.linalg.det(F)) < 1e-12:
                return 0.0
            return -filtered_value(rho, F)
        res = minimize(neg, x0, method="Nelder-Mead", options={"maxiter": 4000, "xatol": 1e-10, "fatol": 1e-13})
        best = max(best, -res.fun)
    return best


def exact_part():
    out = {}
    one = sp.eye(2)
    rho1 = sp.Matrix([[20, 0, 0, 14], [0, 0, 0, 0], [0, 0, 7, 0], [14, 0, 0, 13]]) / 40
    rho2 = sp.Matrix([[441, 0, 0, 56], [0, 49, 0, 0], [0, 0, 1, 0], [56, 0, 0, 9]]) / 500
    for name, rho in (("rho_1", rho1), ("rho_2", rho2)):
        assert all(sp.nsimplify(e) >= 0 for e in rho.eigenvals())
        a, b, T = sp_bloch(rho)
        c, D = canonical_data_exact(a, b, T)
        value, alpha = schur_value_exact(c, D)
        out[name] = {"alpha": str(alpha), "alice_squared_value": str(value)}
    assert out["rho_1"]["alice_squared_value"] == "79/75"
    assert out["rho_2"]["alice_squared_value"] == "32/25"
    # The stated optimal filter of rho_1 applied to the density matrix.
    F = sp.diag(1, 2 / sp.sqrt(17))
    G = sp.kronecker_product(F, one)
    out1 = G * rho1 * G.H
    prob = sp.simplify(out1.trace())
    out1 = sp.simplify(out1 / prob)
    _, _, T1 = sp_bloch(out1)
    TT = sp.Matrix(T1) * sp.Matrix(T1).T
    sv2 = sorted(TT.eigenvals(multiple=True), key=lambda z: -float(z))
    filt = sp.nsimplify(sp.simplify(sv2[0] + sv2[1]))
    assert filt == sp.Rational(79, 75) and prob == sp.Rational(21, 34)
    out["rho_1"].update({"filter_success_probability": str(prob), "filtered_squared_value": str(filt)})
    singlet = sp.Matrix([0, 1, -1, 0]) / sp.sqrt(2)
    zz = sp.Matrix([1, 0, 0, 0])
    family = []
    for p in [sp.Rational(k, 12) for k in range(1, 12)]:
        rho = p * singlet * singlet.T + (1 - p) * zz * zz.T
        a, b, T = sp_bloch(rho)
        c, D = canonical_data_exact(a, b, T)
        A = D * D.T
        alpha = sp.simplify(A.trace() - (c.T * c)[0])
        # rank two: value max(1,(1+alpha)/2); compare with the stated closed form.
        claimed = max(sp.Integer(1), 2 * p / (2 - p))
        rank_two_value = max(sp.Integer(1), (1 + alpha) / 2)
        entry = {"p": str(p), "alpha": str(alpha), "rank_two_value": str(sp.simplify(rank_two_value)),
                 "claimed": str(claimed)}
        if alpha > 1:
            value, _ = schur_value_exact(c, D)
            entry["schur_value"] = str(value)
            assert sp.simplify(value - claimed) == 0
        assert sp.simplify(rank_two_value - claimed) == 0
        family.append(entry)
    out["quasi_distillable_family"] = family
    return out


def numeric_part(seed=20261103, per_rank=40):
    rng = np.random.default_rng(seed)
    records, worst_reconstruction, worst_direct_excess = [], 0.0, -np.inf
    for rank in (1, 2, 3, 4):
        kept = 0
        while kept < per_rank:
            rho = random_state(rng, rank)
            value, alpha, F, vnorm = schur_numeric(rho)
            if alpha <= 1 + 1e-6:
                continue
            kept += 1
            achieved = filtered_value(rho, F)
            direct = direct_max(rho, rng, starts=6 if rank > 1 else 3)
            worst_reconstruction = max(worst_reconstruction, abs(achieved - value))
            worst_direct_excess = max(worst_direct_excess, direct - value)
            records.append({"rank": rank, "alpha": alpha, "schur_value": value,
                            "reconstructed_filter_value": achieved, "direct_maximum": direct,
                            "v_norm": vnorm})
    assert worst_reconstruction < 1e-8, worst_reconstruction
    assert worst_direct_excess < 1e-7, worst_direct_excess
    assert all(r["v_norm"] < 1 for r in records)
    return {"seed": seed, "states": len(records),
            "max_abs_schur_minus_reconstructed_filter": worst_reconstruction,
            "max_direct_minus_schur": worst_direct_excess,
            "min_schur_minus_direct": float(min(r["schur_value"] - r["direct_maximum"] for r in records)),
            "violating_states": sum(r["schur_value"] > 1 for r in records)}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=Path(__file__).with_name("release_check.json"))
    args = parser.parse_args()
    result = {"status": "PASS", "exact": exact_part(), "numeric": numeric_part()}
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
