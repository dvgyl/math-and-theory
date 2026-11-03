"""Finite spectral solver for unilateral two-qubit CHSH filtering.

The mathematical result is exact. This reference implementation uses floating
point linear algebra and therefore is NOT an exact certificate near rank,
degeneracy, or violation thresholds. See theorem.tex and exact_examples.py.
Conventions: B(rho) = sqrt(sigma_1(T)^2 + sigma_2(T)^2); local bound = 1.
Dependencies: numpy, scipy. No continuous filter optimization is performed.
"""
from __future__ import annotations

import numpy as np
from scipy.linalg import null_space
from scipy.optimize import brentq

PAULI = np.array([
    [[1, 0], [0, 1]], [[0, 1], [1, 0]],
    [[0, -1j], [1j, 0]], [[1, 0], [0, -1]],
], dtype=complex)
I3 = np.eye(3)


def cross_matrix(d):
    x, y, z = np.asarray(d, dtype=float)
    return np.array([[0., -z, y], [z, 0., -x], [-y, x, 0.]])


def bloch(rho):
    rho = np.asarray(rho, dtype=complex)
    R = np.array([[np.trace(rho @ np.kron(p, q)).real
                   for q in PAULI] for p in PAULI])
    return R[1:, 0], R[0, 1:], R[1:, 1:]


def state_from_bloch(a, b, T):
    R = np.block([[np.ones((1, 1)), np.asarray(b).reshape(1, 3)],
                  [np.asarray(a).reshape(3, 1), np.asarray(T)]])
    return sum(R[i, j] * np.kron(PAULI[i], PAULI[j])
               for i in range(4) for j in range(4)) / 4


def normalized_chsh_squared(rho):
    T = bloch(rho)[2]
    singular_values = np.linalg.svd(T, compute_uv=False)
    return float(np.sum(singular_values[:2] ** 2))


def sqrt_hermitian(H, inverse=False):
    vals, vecs = np.linalg.eigh((H + H.conj().T) / 2)
    if inverse and np.min(vals) <= 0:
        raise ValueError("Cannot invert a singular marginal.")
    powers = 1 / np.sqrt(vals) if inverse else np.sqrt(np.maximum(vals, 0))
    return (vecs * powers) @ vecs.conj().T


def effect_sqrt(u):
    return sqrt_hermitian(PAULI[0] + np.einsum('i,ijk->jk', u, PAULI[1:]))


def filter_state(rho, F, side="A"):
    G = np.kron(F, PAULI[0]) if side.upper() == "A" else np.kron(PAULI[0], F)
    out = G @ rho @ G.conj().T
    probability = float(np.trace(out).real)
    if probability <= 0:
        raise ValueError("Zero-probability filter.")
    return out / probability, probability


def swap_parties(rho):
    return np.asarray(rho).reshape(2, 2, 2, 2).transpose(1, 0, 3, 2).reshape(4, 4)


def boundary_radius(T, c, tol=1e-11):
    """Exact secular characterization, evaluated numerically; includes hard case."""
    A, d = T @ T.T, T @ c
    alpha, U = np.linalg.eigh(A)
    g = U.T @ d
    top = alpha[-1]
    top_mask = np.abs(alpha - top) <= tol * max(1., abs(top))
    lower = ~top_mask
    x_coordinates = np.zeros(3)
    x_coordinates[lower] = g[lower] / (top - alpha[lower])
    h = float(x_coordinates @ x_coordinates)
    if np.linalg.norm(g[top_mask]) <= tol and h <= 1 + tol:
        x_coordinates[np.flatnonzero(top_mask)[0]] = np.sqrt(max(0., 1 - h))
        multiplier = top
        mode = "hard_case"
    else:
        def secular(z):
            return float(np.sum((g / (z - alpha)) ** 2) - 1)
        low = np.nextafter(top, np.inf)
        high = top + max(1., np.linalg.norm(d))
        while secular(high) > 0:
            high = top + 2 * (high - top)
        multiplier = brentq(secular, low, high, xtol=5e-15, rtol=1e-14)
        x_coordinates = g / (multiplier - alpha)
        x_coordinates /= np.linalg.norm(x_coordinates)
        mode = "secular_root"
    u = U @ x_coordinates
    value = float(np.linalg.norm(c + T.T @ u) ** 2)
    return {"value": value, "u": u, "multiplier": float(multiplier),
            "mode": mode, "finite": False, "kind": "boundary"}


def _clusters(eigenvalues, tol):
    groups = []
    for i, x in enumerate(eigenvalues):
        if not groups or abs(x - eigenvalues[groups[-1][0]]) > tol:
            groups.append([i])
        else:
            groups[-1].append(i)
    return groups


def _exceptional_witness(K, C, tol):
    """Phase-fix a vector in ker(K+iC), including isotropic boundary cases."""
    H = K.astype(complex) + 1j * C
    vals, basis = np.linalg.eigh(H)
    U = basis[:, np.abs(vals) <= tol]
    if U.shape[1] == 0:
        raise ArithmeticError("Exceptional eigenvalue detected without its complex kernel.")
    options = [U[:, i] for i in range(U.shape[1])]
    for i in range(U.shape[1]):
        for j in range(i):
            options.extend([(U[:, i] + U[:, j]) / np.sqrt(2),
                            (U[:, i] + 1j * U[:, j]) / np.sqrt(2)])
    z = max(options, key=lambda w: abs(w @ w))
    bilinear = z @ z
    if abs(bilinear) > tol:
        z = z * np.exp(-0.5j * np.angle(bilinear))
    n, v = z.real.copy(), z.imag.copy()
    if np.linalg.norm(n) < np.linalg.norm(v):
        n, v = v, -n
    scale = np.linalg.norm(n)
    return n / scale, v / scale, bool(abs(bilinear) > tol)


def spectral_candidates(T, c, tol=1e-10):
    """At most three candidate values, using the singular-safe compression."""
    T, c = np.asarray(T, float), np.asarray(c, float)
    A, s, d = T @ T.T, float(c @ c), T @ c
    C = cross_matrix(d)
    K = A - s * I3
    kvals, kvecs = np.linalg.eigh(K)
    eps = tol * max(1., np.linalg.norm(A, 2), s)
    nonzero = np.abs(kvals) > eps
    Kdag = (kvecs[:, nonzero] / kvals[nonzero]) @ kvecs[:, nonzero].T
    N = kvecs[:, ~nonzero]
    CN = C @ N
    # Use the SAME absolute scale for this rank decision. Relative-only SVD
    # thresholds misclassify a mathematically zero CN consisting of roundoff.
    if CN.size:
        cnu, cnsv, cnvh = np.linalg.svd(CN, full_matrices=True)
        cnrank = int(np.sum(cnsv > eps))
        L = cnu[:, cnrank:]
        CNdag = ((cnvh[:cnrank, :].T / cnsv[:cnrank]) @ cnu[:, :cnrank].T
                 if cnrank else np.zeros((N.shape[1], 3)))
    else:
        L = I3.copy()
        CNdag = np.zeros((0, 3))
    if L.shape[1] == 0:
        return []
    M = A + C @ Kdag @ C
    ML = L.T @ M @ L
    vals, vecs = np.linalg.eigh((ML + ML.T) / 2)
    candidates = []
    for group in _clusters(vals, eps):
        mu = float(np.mean(vals[group]))
        E = L @ vecs[:, group]
        if abs(mu - s) <= eps:
            mu = s
            n, v, finite = _exceptional_witness(K, C, 5 * eps)
            minimum_ratio = float(v @ v)
            kind = "exceptional_eigenvalue"
        else:
            correction = np.zeros((3, 3))
            if CN.size:
                correction = N @ CNdag @ (M - mu * I3)
            V = (-Kdag @ C + correction) @ E
            gram_values, gram_vectors = np.linalg.eigh(V.T @ V)
            minimum_ratio = float(gram_values[0])
            if minimum_ratio > 1 + 10 * eps:
                continue
            z = gram_vectors[:, 0]
            n, v = E @ z, V @ z
            finite = bool(v @ v < 1 - 10 * eps)
            kind = "ordinary_eigenvalue"
        u = -np.cross(n, v)
        residual = max(np.linalg.norm(A @ n - C @ v - mu * n),
                       np.linalg.norm(K @ v + C @ n), abs(n @ v),
                       abs(n @ n - 1))
        if residual > 200 * eps:
            raise ArithmeticError(f"Unreliable floating-point branch (residual {residual}).")
        candidates.append({"value": float(np.trace(A) - mu), "eigenvalue": mu,
                           "n": n, "v": v, "u": u, "finite": finite,
                           "minimum_ratio": minimum_ratio, "residual": float(residual),
                           "kind": kind})
    return candidates


def canonical_optimum(T, c, tol=1e-10):
    boundary = boundary_radius(np.asarray(T, float), np.asarray(c, float), tol / 10)
    candidates = spectral_candidates(T, c, tol)
    best = boundary
    for candidate in candidates:
        delta = candidate["value"] - best["value"]
        if delta > 30 * tol or (abs(delta) <= 30 * tol and candidate["finite"]):
            best = candidate
    value = max([boundary["value"]] + [x["value"] for x in candidates])
    return {"value": float(value), "B": float(np.sqrt(max(0., value))),
            "raw_CHSH": float(2 * np.sqrt(max(0., value))),
            "attained_invertibly": bool(best["finite"]),
            "witness": best, "boundary": boundary, "candidates": candidates}


def unilateral_optimum(rho, side="A", tol=1e-10):
    """Return the supremum, an optimal/limiting filter, and success probability."""
    side = side.upper()
    if side not in ("A", "B"):
        raise ValueError("side must be A or B")
    rho = np.asarray(rho, complex)
    working = rho if side == "A" else swap_parties(rho)
    a, b, _ = bloch(working)
    # Partial trace avoids loss of a small eigenvalue through 1-|a| subtraction.
    marginal = np.trace(working.reshape(2, 2, 2, 2), axis1=1, axis2=3)
    marginal_values = np.linalg.eigvalsh(marginal)
    if marginal_values[0] <= tol:
        other = np.trace(working.reshape(2, 2, 2, 2), axis1=0, axis2=2)
        if marginal_values[0] == 0 and np.array_equal(working, np.kron(marginal, other)):
            # Exact structural product check, not a small-eigenvalue approximation.
            value = float(b @ b)
            return {"value": value, "B": np.sqrt(value), "raw_CHSH": 2 * np.sqrt(value),
                    "attained_invertibly": True, "filter": PAULI[0].copy(),
                    "probability": 1., "kind": "pure_marginal"}
        raise ArithmeticError(
            "Near-singular marginal: floating-point rank decisions can change the "
            "answer discontinuously. Use exact arithmetic/the pure-marginal theorem "
            "or higher precision; this routine will not silently treat it as pure.")
    W = sqrt_hermitian(2 * marginal, inverse=True)
    canonical, _ = filter_state(working, W, "A")
    ac, c, T = bloch(canonical)
    if np.linalg.norm(ac) > 100 * tol:
        raise ArithmeticError("Marginal whitening failed its numerical residual check.")
    result = canonical_optimum(T, c, tol)
    u = result["witness"]["u"]
    # Scaling does not affect the normalized output. This chooses max success.
    F = effect_sqrt(u) @ W
    F /= np.linalg.norm(F, 2)
    output, probability = filter_state(rho, F, side)
    result.update({"filter": F, "probability": probability, "canonical_T": T,
                   "canonical_c": c, "output": output,
                   "density_matrix_witness_value": normalized_chsh_squared(output)})
    return result


if __name__ == "__main__":
    rho = np.array([[20, 0, 0, 14], [0, 0, 0, 0],
                    [0, 0, 7, 0], [14, 0, 0, 13]], dtype=complex) / 40
    print("Initial B^2:", normalized_chsh_squared(rho))
    for side in ("A", "B"):
        result = unilateral_optimum(rho, side)
        print(side, "sup B^2 =", result["value"], "finite =", result["attained_invertibly"],
              "success probability =", result["probability"])
