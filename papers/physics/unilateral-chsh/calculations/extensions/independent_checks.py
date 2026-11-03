"""Independent numerical audit of the round-two unilateral CHSH extensions.

Only NumPy and SciPy are required. This script is intentionally independent
of extensions_solver.py: every comparison optimizer filters a complex 4x4
density matrix and recomputes the correlation singular values. Agreement is
numerical evidence, not a replacement for the proofs or the Lean audit.

Run: python3 independent_checks.py
"""
import json
from pathlib import Path

import numpy as np
from scipy.optimize import minimize, minimize_scalar


SEED = 861702406
SIGMA = np.array([[[0, 1], [1, 0]], [[0, -1j], [1j, 0]],
                  [[1, 0], [0, -1]]], dtype=complex)
I2 = np.eye(2, dtype=complex)
I3 = np.eye(3)
SA = np.array([np.kron(s, I2) for s in SIGMA])
SB = np.array([np.kron(I2, s) for s in SIGMA])
SS = np.array([[np.kron(s, t) for t in SIGMA] for s in SIGMA])
SPIN = np.kron(SIGMA[1], SIGMA[1])


def density(c, D):
    return (np.eye(4) + np.einsum("i,ijk->jk", c, SB)
            + np.einsum("ij,ijkl->kl", D, SS)) / 4


def partial_a(rho):
    """The state on Alice, after tracing out Bob."""
    return np.trace(rho.reshape(2, 2, 2, 2), axis1=1, axis2=3)


def partial_b(rho):
    return np.trace(rho.reshape(2, 2, 2, 2), axis1=0, axis2=2)


def bloch(rho):
    a = np.einsum("ab,iba->i", rho, SA).real
    b = np.einsum("ab,iba->i", rho, SB).real
    T = np.einsum("ab,ijba->ij", rho, SS).real
    return a, b, T


def sqrt_psd(X):
    e, V = np.linalg.eigh(X)
    return (V * np.sqrt(np.maximum(e, 0))) @ V.conj().T


def canonical(rho):
    e, V = np.linalg.eigh(2 * partial_a(rho))
    F = (V * (1 / np.sqrt(e))) @ V.conj().T
    FF = np.kron(F, I2)
    out = FF @ rho @ FF.conj().T
    return out / np.trace(out), F


def chsh_squared(rho):
    T = bloch(rho)[2]
    sv = np.linalg.svd(T, compute_uv=False)
    return float(sv[0]**2 + sv[1]**2)


def direct_filtered(rho, u):
    # Kraus operator is obtained from an actual Hermitian 2x2 effect.
    F = sqrt_psd(I2 + np.einsum("i,ijk->jk", u, SIGMA))
    FF = np.kron(F, I2)
    out = FF @ rho @ FF.conj().T
    return chsh_squared(out / np.trace(out))


def direct_max(rho, R, rng, starts=9):
    if R == 0:
        return chsh_squared(rho), np.zeros(3)

    def objective(w):
        u = np.array(w, copy=True)
        norm = np.linalg.norm(u)
        if norm > R:
            u *= R / norm
        return -direct_filtered(rho, u)

    best = (-1.0, None)
    for j in range(starts):
        u = np.zeros(3) if j == 0 else rng.normal(size=3)
        if j:
            u *= rng.uniform(0, R) / np.linalg.norm(u)
        ans = minimize(objective, u, method="SLSQP",
                       constraints={"type": "ineq", "fun": lambda v: R*R-v@v},
                       options={"ftol": 2e-12, "maxiter": 220})
        u = ans.x
        if np.linalg.norm(u) > R:
            u *= R / np.linalg.norm(u)
        value = direct_filtered(rho, u)
        if value > best[0]:
            best = (value, u)
    return best


def cross(d):
    x, y, z = d
    return np.array([[0, -z, y], [z, 0, -x], [-y, x, 0]])


def delta_b(rho):
    rb = partial_b(rho)
    return float(np.trace(rho @ rho - np.zeros_like(rho)).real - np.trace(rb @ rb).real)


def adjugate3(X):
    # Cofactor construction, independent of inverse/determinant division.
    out = np.empty((3, 3))
    for i in range(3):
        for j in range(3):
            out[j, i] = (-1)**(i+j) * np.linalg.det(np.delete(np.delete(X, i, 0), j, 1))
    return out


def scalar_psd_tests(X):
    return np.array([np.trace(X),
                     (np.trace(X)**2 - np.trace(X @ X))/2,
                     np.linalg.det(X)])


def data(rho):
    _, c, D = bloch(rho)
    A = D @ D.T
    s = c @ c
    d = D @ c
    C = cross(d)
    K = A - s*I3
    return c, D, A, s, d, C, K


def shortcut(rho):
    c, D, A, s, d, C, K = data(rho)
    M = A + C @ np.linalg.solve(K, C)
    vals, vecs = np.linalg.eigh(M)
    n = vecs[:, 0]
    v = -np.linalg.solve(K, C @ n)
    u = -np.cross(n, v)
    return float(np.trace(A)-vals[0]), u, n, v, M


def dual_value(rho, R):
    c, D, A, s, d, C, K = data(rho)
    if R == 0:
        return float(np.trace(A)-np.linalg.eigvalsh(A)[0]), float("inf")

    def eigendata(tau):
        P = K + tau*I3
        M = A + C @ np.linalg.solve(P, C)
        vals, vecs = np.linalg.eigh(M)
        group = abs(vals-vals[0]) < 1e-10
        N = vecs[:, group]
        V = -np.linalg.solve(P, C @ N)
        radius = float(np.linalg.eigvalsh(V.T @ V)[0])
        return vals[0], radius

    def objective(tau):
        return float(np.trace(A)+tau*R*R-eigendata(tau)[0])

    if eigendata(0)[1] <= R*R + 1e-13:
        return objective(0), 0.0
    hi = 1.0
    while eigendata(hi)[1] > R*R:
        hi *= 2
    result = minimize_scalar(objective, bounds=(0, hi), method="bounded",
                             options={"xatol": 1e-13, "maxiter": 500})
    return min(objective(0), result.fun), float(result.x)


def random_state(rng, rank):
    X = rng.normal(size=(4, rank)) + 1j*rng.normal(size=(4, rank))
    rho = X @ X.conj().T
    return rho/np.trace(rho)


def main():
    rng = np.random.default_rng(SEED)
    maxima = {}
    minima = {"gram_eigenvalue": 1.0, "purity_slack": 1.0,
              "automatic_radius_margin": 1.0}
    counts = {"random_states": 0, "purity_positive": 0, "gram_positive": 0,
              "polynomial_decisions": 0, "axial_states": 0}
    frontier_states = []

    def residual(name, value):
        maxima[name] = max(maxima.get(name, 0.0), float(abs(value)))

    for rank in [1, 2, 3, 4]:
        for index in range(250):
            raw = random_state(rng, rank)
            rho, F0 = canonical(raw)
            a, b, T = bloch(raw)
            c, D, A, s, d, C, K = data(rho)
            alpha = np.trace(A)-s
            m = (alpha-1)/2
            flipped = SPIN @ rho.T @ SPIN
            G = np.array([[np.trace(rho @ SA[i] @ flipped @ SA[j])
                           for j in range(3)] for i in range(3)])
            residual("gram_identity", np.linalg.norm(2*G-(K-m*I3+1j*C)))
            minima["gram_eigenvalue"] = min(minima["gram_eigenvalue"],
                                             float(np.linalg.eigvalsh(G)[0]))
            counts["gram_positive"] += np.linalg.eigvalsh(G)[0] >= -1e-10

            n = rng.normal(size=3); n /= np.linalg.norm(n)
            v = rng.normal(size=3)
            z = n + 1j*v
            real_pair = n@(K-m*I3)@n + v@(K-m*I3)@v + 2*v@C@n
            residual("real_pair_sign", z.conj()@(K-m*I3+1j*C)@z-real_pair)
            raw_flip = SPIN @ raw.T @ SPIN
            N = np.einsum("i,ijk->jk", n, SA)
            overlap = np.trace(raw @ N @ raw_flip @ N).real
            lhs = np.sum(T*T)-np.linalg.norm(T.T@n)**2+(a@n)**2+2*overlap
            residual("plane_identity", lhs-(1+2*delta_b(raw)))

            F = rng.normal(size=(2, 2)) + 1j*rng.normal(size=(2, 2))
            FF = np.kron(F, I2)
            filtered = FF @ raw @ FF.conj().T
            residual("determinant_covariance", delta_b(filtered)-abs(np.linalg.det(F))**2*delta_b(raw))
            residual("raw_alpha_identity", alpha-(np.sum(T*T)-b@b)/(1-a@a))

            X = T-np.outer(a, b)
            h = 1-a@a
            Qraw = X.T @ (I3+np.outer(a, a)/h) @ X/h
            craw = (b-T.T@a)/h
            residual("raw_ellipsoid_center", np.linalg.norm(c-craw))
            residual("raw_ellipsoid_shape", np.linalg.norm(D.T@D-Qraw))

            u = rng.normal(size=3); u *= rng.uniform(0, .95)/np.linalg.norm(u)
            actual = direct_filtered(rho, u)
            slack = 1+m*(1-u@u)-actual
            minima["purity_slack"] = min(minima["purity_slack"], float(slack))
            rootarg = (1-a@u)**2-(1-a@a)*(1-u@u)
            psuccess = (1-a@a)/(1-a@u+np.sqrt(max(0, rootarg)))
            effect = F0 @ (I2+np.einsum("i,ijk->jk", u, SIGMA)) @ F0
            residual("original_success_probability", psuccess-1/np.linalg.eigvalsh(effect)[-1])

            if alpha > 1+1e-9:
                counts["purity_positive"] += 1
                optimum, ustar, nstar, vstar, M = shortcut(rho)
                delta = np.linalg.eigvalsh(M)[0]-s
                residual("rayleigh_norm_identity", vstar@(M-s*I3)@vstar
                         -delta+delta*delta*nstar@np.linalg.solve(K, nstar))
                residual("automatic_orthogonality", nstar@vstar)
                minima["automatic_radius_margin"] = min(minima["automatic_radius_margin"],
                                                          float(1-vstar@vstar))
                residual("shortcut_filter_attainment", direct_filtered(rho, ustar)-optimum)
                if rank > 1 and len(frontier_states) < 14 and np.linalg.norm(ustar) > .04:
                    frontier_states.append(rho)

                detK = np.linalg.det(K)
                q = d@K@d
                residual("cross_product_inverse_identity", np.linalg.norm(
                    C@np.linalg.solve(K, C)-(np.outer(K@d, K@d)-q*K)/detK))
                t = np.trace(A)-1
                R = detK*(A-t*I3)+C@adjugate3(K)@C
                residual("polynomial_matrix", np.linalg.norm(R-detK*(M-t*I3)))
                Q = D.T@D
                Qs = Q-s*I3
                detQ = np.linalg.det(Q)
                RE = detQ*(detK-q)*I3+(s*q-t*detK)*adjugate3(Q)
                RE += detQ*np.outer(Qs@c, Qs@c)
                Dinv = np.linalg.inv(D)
                residual("ellipsoid_congruence", np.linalg.norm(RE-detQ*Dinv@R@Dinv.T))
                # Away from equality, compare all three certificate forms.
                if abs(optimum-1) > 1e-6:
                    activate = optimum > 1
                    assert (np.linalg.eigvalsh(R)[0] < 0) == activate
                    assert (np.linalg.eigvalsh(RE)[0] < 0) == activate
                    assert (min(scalar_psd_tests(RE)) < 0) == activate
                    counts["polynomial_decisions"] += 1
            counts["random_states"] += 1

    # Explicit physical counterexample: K positive alone does not permit
    # dropping the minimum-eigenvector feasibility checks.
    counterexample = np.array([[19, 0, 0, 7], [0, 1, 0, 0],
                              [0, 0, 7, 0], [7, 0, 0, 13]], complex)/40
    false_value, _, _, false_v, _ = shortcut(counterexample)
    counter_direct = direct_max(counterexample, 1, rng, starts=30)[0]
    residual("counterexample_false_formula", false_value-7693/5200)
    residual("counterexample_infeasible_radius", np.linalg.norm(false_v)-72/13)
    residual("counterexample_actual_optimum", counter_direct-81/100)

    # Physical phase-covariant channels. Independent direct filtering is used
    # on a representative subset, not merely the same shortcut formula.
    axial_records = []
    for index in range(600):
        r = rng.uniform(0, 1)
        c0 = rng.uniform(0, 1-r)
        x = rng.uniform(0, ((1+r)**2-c0*c0)/4)
        rho = density(np.array([0, 0, c0]), np.diag([np.sqrt(x), -np.sqrt(x), r]))
        assert np.linalg.eigvalsh(rho)[0] >= -1e-12
        predicted = bool(x > .5 or (r > 1-x and c0*c0 > x*(1-x-r*r)/(1-x)))
        alpha = 2*x+r*r-c0*c0
        if alpha > 1+1e-10:
            value, ustar, _, _, _ = shortcut(rho)
            formula = max(2*x, x+x*r*r/(x-c0*c0))
            residual("axial_closed_formula", value-formula)
            assert predicted == (value > 1)
        else:
            assert not predicted
        if index < 36:
            direct = direct_max(rho, 1, rng, starts=10)[0]
            assert predicted == (direct > 1+1e-7), (r, c0, x, direct, predicted)
            axial_records.append({"r": r, "c": c0, "x": x,
                                  "predicted_activation": predicted, "direct": direct})
        counts["axial_states"] += 1

    # Add fixed states and a positive-Gram state below the purity-positive
    # regime, to test the stated broader domain of the constrained dual.
    frontier_states.append(np.array([[20, 0, 0, 14], [0, 0, 0, 0],
                                    [0, 0, 7, 0], [14, 0, 0, 13]], complex)/40)
    frontier_states.append(density(np.array([0, 0, .05]), np.diag([.4, -.35, .3])))
    frontier_states.append(density(np.zeros(3), np.diag([.65, -.65, .65])))
    frontier_records = []
    for index, rho in enumerate(frontier_states):
        *_, C, K = data(rho)
        assert np.linalg.eigvalsh(K+1j*C)[0] > 0
        for R in [0, .1, .25, .5, .8, 1.0]:
            dual, tau = dual_value(rho, R)
            direct, u = direct_max(rho, R, rng, starts=9)
            gap = dual-direct
            if abs(gap) > 3e-7:
                direct, u = direct_max(rho, R, rng, starts=35)
                gap = dual-direct
            residual("constrained_dual_direct_gap", gap)
            frontier_records.append({"state": index, "R": R, "dual": dual,
                                     "direct": direct, "gap": gap,
                                     "tau": tau if np.isfinite(tau) else None,
                                     "direct_effect_norm": float(np.linalg.norm(u))})
            assert gap > -1e-7 and gap < 2e-6, frontier_records[-1]

    assert maxima["gram_identity"] < 1e-10
    assert maxima["real_pair_sign"] < 1e-10
    assert maxima["plane_identity"] < 1e-10
    assert maxima["determinant_covariance"] < 1e-8
    assert minima["gram_eigenvalue"] > -1e-10
    assert minima["purity_slack"] > -1e-10
    assert minima["automatic_radius_margin"] > 0
    assert maxima["shortcut_filter_attainment"] < 1e-9
    report = {"seed": SEED, "counts": {k: int(v) for k, v in counts.items()},
              "maximum_residuals": maxima, "minimum_margins": minima,
              "success_frontier_comparisons": len(frontier_records),
              "frontier_records": frontier_records, "axial_direct_records": axial_records,
              "counterexample": {"actual_direct": counter_direct, "exact": .81,
                                 "unguarded_false_value": false_value,
                                 "false_effect_radius": float(np.linalg.norm(false_v))}}
    path = Path(__file__).with_name("independent_results.json")
    path.write_text(json.dumps(report, indent=2))
    print(json.dumps({k: v for k, v in report.items()
                      if k not in ["frontier_records", "axial_direct_records"]}, indent=2))


if __name__ == "__main__":
    main()
