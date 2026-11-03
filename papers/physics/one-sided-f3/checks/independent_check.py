#!/usr/bin/env python3
"""Independent numerical audit of exact one-sided filtered F3 formulas.

This implementation was written independently of the main implementation.  It
whitens the density matrix itself, uses its own trust-region solver, recovers a
2x2 physical Kraus filter, and recomputes the answer directly from the filtered
4x4 matrix.  Numerical checks are evidence, not a replacement for the proof.

Dependencies: numpy, scipy.  Run: python independent_check.py
"""

from __future__ import annotations

import json
import math
import platform
from pathlib import Path

import numpy as np
import scipy
from numpy.linalg import eigh, norm
from scipy.optimize import brentq, minimize


SEED = 240603945
I2 = np.eye(2, dtype=complex)
P = np.array(
    [
        [[0, 1], [1, 0]],
        [[0, -1j], [1j, 0]],
        [[1, 0], [0, -1]],
    ],
    dtype=complex,
)
PP = np.array([[np.kron(p, q) for q in P] for p in P])


def herm_sqrt(a: np.ndarray) -> np.ndarray:
    w, u = eigh((a + a.conj().T) / 2)
    if w.min() < -1e-9:
        raise ValueError("Negative filter-effect eigenvalue")
    return (u * np.sqrt(np.maximum(w, 0))) @ u.conj().T


def marginal(rho: np.ndarray, side: int) -> np.ndarray:
    # Tensor indices are (Alice row, Bob row, Alice col, Bob col).
    rt = rho.reshape(2, 2, 2, 2)
    return np.einsum("ijkj->ik", rt) if side == 0 else np.einsum("ijil->jl", rt)


def bloch(r: np.ndarray) -> np.ndarray:
    return np.array([np.trace(r @ s).real for s in P])


def corr(rho: np.ndarray) -> np.ndarray:
    return np.array([[np.trace(rho @ PP[i, j]).real for j in range(3)] for i in range(3)])


def density_filter(rho: np.ndarray, f: np.ndarray, side: int) -> tuple[np.ndarray, float]:
    ff = np.kron(f, I2) if side == 0 else np.kron(I2, f)
    raw = ff @ rho @ ff.conj().T
    prob = float(np.trace(raw).real)
    if prob <= 1e-15:
        raise ValueError("Zero-probability postselection")
    return raw / prob, prob


def f3_squared(rho: np.ndarray) -> float:
    t = corr(rho)
    return float(np.sum(t * t))


def filter_from_effect_vector(v: np.ndarray) -> np.ndarray:
    return herm_sqrt(I2 + np.tensordot(v, P, axes=1))


def ball_quadratic(h: np.ndarray, g: np.ndarray) -> dict:
    """Maximize x' H x + 2 g' x on the unit ball, independently.

    Includes negative-semidefinite interior, zero curvature, secular boundary,
    and singular hard cases.  Thresholds affect only this numerical audit.
    """
    w, u = eigh((h + h.T) / 2)
    d = u.T @ g
    lower = max(0.0, float(w[-1]))
    gap = lower - w
    tol = 2e-12 * max(1.0, norm(h), norm(g))
    zero = np.abs(gap) <= tol
    z = np.zeros(3)
    z[~zero] = d[~zero] / gap[~zero]
    pole = bool(np.any(np.abs(d[zero]) > tol))
    need_root = pole or float(z @ z) > 1 + 5e-11

    if need_root:
        def sec(lam: float) -> float:
            # An infinite value at the first representable point above a pole
            # is the correct sign for bracketing the secular root.
            with np.errstate(over="ignore", divide="ignore", invalid="ignore"):
                return float(np.sum((d / (lam - w)) ** 2) - 1)

        lo = np.nextafter(lower, math.inf)
        hi = max(lower + 1.0, 1.0)
        while sec(hi) > 0:
            hi = 2 * hi + 1
        lam = float(brentq(sec, lo, hi, xtol=2e-14, rtol=4 * np.finfo(float).eps))
        z = d / (lam - w)
        branch = "secular_boundary"
    else:
        lam = lower
        if lam > tol:
            # Complementarity requires a boundary point; top eigenspace is free.
            inds = np.flatnonzero(zero)
            if not len(inds):
                raise AssertionError("Boundary completion lacks a nullspace")
            z[inds[0]] = math.sqrt(max(0.0, 1.0 - float(z @ z)))
            branch = "hard_boundary"
        else:
            branch = "interior_or_flat"
    x = u @ z
    val = float(x @ h @ x + 2 * g @ x)
    mat = lam * np.eye(3) - h
    return {
        "value": val,
        "x": x,
        "lambda": lam,
        "branch": branch,
        "stationarity": float(norm(mat @ x - g)),
        "psd_min": float(eigh(mat)[0][0]),
        "complementarity": abs(lam * (1 - float(x @ x))),
    }


def exact_by_density_canonicalization(rho: np.ndarray, side: int) -> dict:
    """Recover maximum/supremum and a contraction filter without Bloch whitening."""
    red = marginal(rho, side)
    w, u = eigh(red)
    if w[0] < 5e-13:
        # A genuinely rank-one marginal forces an exact product.  Proximity to
        # this case is insufficient: arbitrarily weak pure-state entanglement
        # still has one-sided filtered F3=sqrt(3).  Be conservative and reject
        # floating-point data that cannot be distinguished reliably here.
        other = marginal(rho, 1 - side)
        product = np.kron(red, other) if side == 0 else np.kron(other, red)
        if w[0] == 0.0 and np.array_equal(rho, product):
            c = bloch(other)
            return {
                "value": float(c @ c),
                "filter": I2.copy(),
                "canonical": rho,
                "branch": "pure_filtered_marginal",
                "lambda": None,
                "x": None,
                "stationarity": 0.0,
                "psd_min": 0.0,
                "complementarity": 0.0,
            }
        raise ArithmeticError(
            "Near-pure or numerically singular marginal: use exact or higher-precision "
            "arithmetic; no tolerance-based pure-product substitution is permitted."
        )
    whiten = (u * (1 / np.sqrt(2 * w))) @ u.conj().T
    rc, _ = density_filter(rho, whiten, side)
    t = corr(rc)
    if side == 1:
        t = t.T
    c = bloch(marginal(rc, 1 - side))
    base = float(np.sum(t * t))
    h = t @ t.T + (float(c @ c) - base) * np.eye(3)
    g = t @ c
    sol = ball_quadratic(h, g)
    # Every physical filter is a positive effect square root times whitening,
    # followed by an irrelevant output unitary and an overall scale.
    f = filter_from_effect_vector(sol["x"]) @ whiten
    scale = norm(f, 2)
    f = f / scale
    sol.update({"value": base + sol["value"], "filter": f, "canonical": rc})
    return sol


def algebraic_original_objective(rho: np.ndarray, v: np.ndarray, side: int) -> float:
    """Separately check the fractional quadratic identity in original coordinates."""
    t = corr(rho)
    if side == 1:
        t = t.T
    a = bloch(marginal(rho, side))
    b = bloch(marginal(rho, 1 - side))
    z = float(np.sum(t * t))
    n = z + 2 * float(v @ t @ b) + float(v @ (t @ t.T + (b @ b - z) * np.eye(3)) @ v)
    return n / (1 + float(a @ v)) ** 2


def independent_optimizer(rho: np.ndarray, side: int, rng: np.random.Generator) -> dict:
    """Multistart SLSQP of direct 4x4 filtering, no trust-region formula."""
    def obj(v: np.ndarray) -> float:
        r = norm(v)
        # During infeasible SLSQP trial steps, radially project so the effect is PSD.
        if r > 1:
            v = v / r
        f = filter_from_effect_vector(v)
        rr, _ = density_filter(rho, f, side)
        return -f3_squared(rr)

    starts = [np.zeros(3)]
    for _ in range(5):
        v = rng.normal(size=3)
        starts.append(v / norm(v) * rng.uniform(0.25, 0.95))
    best = -math.inf
    success = 0
    for st in starts:
        res = minimize(
            obj,
            st,
            method="SLSQP",
            constraints=[{"type": "ineq", "fun": lambda v: 1 - float(v @ v), "jac": lambda v: -2 * v}],
            options={"ftol": 2e-11, "maxiter": 220},
        )
        success += int(res.success)
        if norm(res.x) <= 1 + 1e-6:
            best = max(best, -obj(res.x))
    return {"value": best, "successful_starts": success, "total_starts": len(starts)}


def wishart(rng: np.random.Generator, rank: int) -> np.ndarray:
    a = rng.normal(size=(4, rank)) + 1j * rng.normal(size=(4, rank))
    r = a @ a.conj().T
    return r / np.trace(r)


def from_bloch(a: np.ndarray, b: np.ndarray, t: np.ndarray) -> np.ndarray:
    r = np.kron(I2, I2)
    for i in range(3):
        r = r + a[i] * np.kron(P[i], I2) + b[i] * np.kron(I2, P[i])
        for j in range(3):
            r = r + t[i, j] * PP[i, j]
    return r / 4


def main() -> dict:
    rng = np.random.default_rng(SEED)
    out = {
        "seed": SEED,
        "python": platform.python_version(),
        "numpy": np.__version__,
        "scipy": scipy.__version__,
        "meaning": "Independent floating-point checks; not a formal or exhaustive proof.",
        "random_states_per_rank": 60,
        "ranks": [1, 2, 3, 4],
        "one_sided_cases": 0,
        "direct_recovery_max_absolute_error": 0.0,
        "original_fractional_identity_max_absolute_error": 0.0,
        "optimality_stationarity_max": 0.0,
        "optimality_psd_min": 0.0,
        "optimality_complementarity_max": 0.0,
        "optimizer_comparisons": 0,
        "optimizer_max_absolute_gap": 0.0,
        "optimizer_max_excess_over_formula": 0.0,
        "optimizer_successful_starts": 0,
        "optimizer_total_starts": 0,
        "failures": [],
        "branches": {},
        "named_cases": [],
    }

    def audit_case(rho: np.ndarray, label: str, expected=None, optimize=False):
        if eigh(rho)[0][0] < -1e-11:
            raise AssertionError(f"Nonphysical input {label}")
        vals = []
        for side in (0, 1):
            sol = exact_by_density_canonicalization(rho, side)
            filtered, prob = density_filter(rho, sol["filter"], side)
            actual = f3_squared(filtered)
            err = abs(actual - sol["value"])
            out["one_sided_cases"] += 1
            out["direct_recovery_max_absolute_error"] = max(out["direct_recovery_max_absolute_error"], err)
            out["optimality_stationarity_max"] = max(out["optimality_stationarity_max"], sol["stationarity"])
            out["optimality_psd_min"] = min(out["optimality_psd_min"], sol["psd_min"])
            out["optimality_complementarity_max"] = max(out["optimality_complementarity_max"], sol["complementarity"])
            branch = sol["branch"]
            out["branches"][branch] = out["branches"].get(branch, 0) + 1
            if err > 2e-8 or sol["value"] > 3 + 1e-8 or sol["value"] < -1e-9:
                out["failures"].append({"case": label, "side": side, "type": "direct_recovery", "error": err})
            if expected is not None and abs(sol["value"] - expected[side]) > 2e-9:
                out["failures"].append({"case": label, "side": side, "type": "known_value", "value": sol["value"], "expected": expected[side]})
            for _ in range(3):
                v = rng.normal(size=3)
                v *= rng.uniform(0, 0.98) / norm(v)
                filt, _ = density_filter(rho, filter_from_effect_vector(v), side)
                direct = f3_squared(filt)
                frac = algebraic_original_objective(rho, v, side)
                diff = abs(direct - frac)
                out["original_fractional_identity_max_absolute_error"] = max(out["original_fractional_identity_max_absolute_error"], diff)
                if diff > 2e-8:
                    out["failures"].append({"case": label, "side": side, "type": "fractional_identity", "error": diff})
                if direct > sol["value"] + 2e-8:
                    out["failures"].append({"case": label, "side": side, "type": "random_filter_exceeds", "excess": direct - sol["value"]})
            if optimize:
                opt = independent_optimizer(rho, side, rng)
                gap = sol["value"] - opt["value"]
                out["optimizer_comparisons"] += 1
                out["optimizer_max_absolute_gap"] = max(out["optimizer_max_absolute_gap"], abs(gap))
                out["optimizer_max_excess_over_formula"] = max(out["optimizer_max_excess_over_formula"], -gap)
                out["optimizer_successful_starts"] += opt["successful_starts"]
                out["optimizer_total_starts"] += opt["total_starts"]
                if abs(gap) > 2e-6:
                    out["failures"].append({"case": label, "side": side, "type": "optimizer_gap", "gap": gap})
            vals.append({"squared_value": sol["value"], "branch": branch, "success_probability": prob, "filter_rank": int(np.linalg.matrix_rank(sol["filter"], tol=1e-7)), "lambda": sol["lambda"]})
        return vals

    for rank in (1, 2, 3, 4):
        for j in range(out["random_states_per_rank"]):
            audit_case(wishart(rng, rank), f"Wishart_rank{rank}_{j}", optimize=(j < 8))

    # Named edge cases and exact values, with both local filtering choices.
    zero = np.zeros(3)
    pure0 = np.diag([1, 0]).astype(complex)
    mix04 = (I2 + 0.4 * P[2]) / 2
    mix03 = (I2 + 0.3 * P[0]) / 2
    cases = [
        ("maximally_mixed", np.eye(4) / 4, [0, 0]),
        ("both_pure_product", np.kron(pure0, pure0), [1, 1]),
        ("pure_A_mixed_B", np.kron(pure0, mix04), [0.16, 1]),
        ("mixed_A_pure_B", np.kron(mix04, pure0), [1, 0.16]),
        ("both_mixed_product", np.kron(mix03, mix04), [0.16, 0.09]),
        ("rank_one_correlation_flat", from_bloch(zero, zero, np.diag([0, 0, 0.6])), [0.36, 0.36]),
        ("hard_boundary_nonzero_g", from_bloch(zero, np.array([0.3, 0, 0]), np.diag([0.01, -0.05, 0.08])), None),
    ]
    bell = np.array([1, 0, 0, 1], dtype=complex) / np.sqrt(2)
    bellrho = np.outer(bell, bell.conj())
    for p in (0, 0.1, 0.5, 1 / math.sqrt(3), 0.9, 1):
        cases.append((f"Werner_{p:.9f}", p * bellrho + (1 - p) * np.eye(4) / 4, [3 * p * p] * 2))
    for c in (0, 0.3, 0.6, 1):
        # Canonical amplitude-damping Choi state; physical for 0<=c<=1.
        cases.append((f"amplitude_damping_{c}", from_bloch(zero, np.array([0, 0, c]), np.diag([math.sqrt(1-c), -math.sqrt(1-c), 1-c])), None))
    for label, rho, expected in cases:
        vals = audit_case(rho, label, expected=expected, optimize=False)
        out["named_cases"].append({"case": label, "by_side_A_B": vals})

    # Bare TRS edge cases independently check pseudoinverse completion logic.
    trs_cases = [
        ("hard_positive_multiplier", np.diag([0.5, 0.5, 0.1]), np.array([0, 0, 0.2]), 0.6),
        ("negative_semidefinite_flat", np.diag([0, -1, -2]), np.array([0, 0.25, 0]), 0.0625),
        ("zero_hessian", np.zeros((3, 3)), np.array([0.3, 0.4, 0]), 1.0),
        ("zero_problem", np.zeros((3, 3)), np.zeros(3), 0.0),
    ]
    out["direct_trs_edge_cases"] = []
    for name, h, g, expected in trs_cases:
        sol = ball_quadratic(h, g)
        error = abs(sol["value"] - expected)
        out["direct_trs_edge_cases"].append({"name": name, "value": sol["value"], "expected": expected, "branch": sol["branch"], "error": error})
        if error > 1e-10:
            out["failures"].append({"case": name, "type": "TRS_known_value", "error": error})

    # Regression: tiny entanglement cannot be replaced by a pure-product
    # marginal merely because a Bloch coordinate rounds to one.  Float64 cannot
    # safely perform this whitening, so the documented behavior is rejection.
    out["near_pure_precision_guards"] = []
    for epsilon in (1e-14, 1e-24):
        psi = np.array([math.sqrt(1 - epsilon), 0, 0, math.sqrt(epsilon)], dtype=complex)
        rho = np.outer(psi, psi.conj())
        for side in (0, 1):
            try:
                exact_by_density_canonicalization(rho, side)
            except ArithmeticError:
                out["near_pure_precision_guards"].append({"epsilon": epsilon, "side": side, "correctly_rejected": True})
            else:
                out["failures"].append({"case": "near_pure_entangled", "epsilon": epsilon, "side": side, "type": "missing_precision_guard"})
    out["failure_count"] = len(out["failures"])
    dest = Path(__file__).with_name("independent_results.json")
    dest.write_text(json.dumps(out, indent=2) + "\n")
    print(json.dumps({k: v for k, v in out.items() if k not in ("named_cases", "direct_trs_edge_cases")}, indent=2))
    return out


if __name__ == "__main__":
    result = main()
    raise SystemExit(1 if result["failure_count"] else 0)
