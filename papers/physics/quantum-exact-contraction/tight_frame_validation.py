"""Diagnostic checks of the explicit all-dimension trace-gap witness.

These floating-point checks supplement the analytic proof; they are not a
proof or a replacement for the Lean verification.
"""
import json
import numpy as np

if not __debug__:
    raise RuntimeError("Run without Python optimization so diagnostic assertions remain enabled")


def trace_norm(x):
    return float(np.abs(np.linalg.eigvalsh(x)).sum())


def frame_witness(n, u):
    phase = np.exp(2j * np.pi * np.arange(n) / n)
    z = np.array([np.ones(n), phase]) / np.sqrt(2)
    zm = np.array([np.ones(n), -phase]) / np.sqrt(2)
    p = np.eye(n) - (2 / n) * z.conj().T @ z
    rdim = 2 * n + 2
    vp = np.zeros((rdim, n), complex)
    vm = np.zeros((rdim, n), complex)
    vp[:n] = p
    vp[n:n + 2] = u * z
    vm[n:n + 2] = u * zm
    vm[n + 2:] = p
    plus = np.array([np.outer(vp[:, i], vp[:, i].conj()) for i in range(n)])
    minus = np.array([np.outer(vm[:, i], vm[:, i].conj()) for i in range(n)])
    x = plus - minus
    marginal = np.zeros((rdim, rdim), complex)
    marginal[:n, :n] = p
    marginal[n + 2:, n + 2:] = -p
    return p, vp, vm, plus, minus, x, marginal


def bell_family(d):
    out = []
    for a in range(d):
        for b in range(d):
            v = np.zeros(d * d, complex)
            for x in range(d):
                v[x * d + ((x + b) % d)] = np.exp(2j * np.pi * a * x / d) / np.sqrt(d)
            out.append(np.outer(v, v.conj()))
    return np.array(out)


def validate(n, s, u, bell=False):
    p, vp, vm, plus, minus, x, marginal = frame_witness(n, u)
    r = (n - 2) / n
    b = (1 + s) / n
    a = b - s * r
    norm = n * (r + u * u)
    y = b * marginal - s * x
    in_gap = sum(map(trace_norm, x)) - trace_norm(marginal)
    out_gap = sum(map(trace_norm, y)) - trace_norm(marginal)
    formula = (np.sqrt((a + s * u * u) ** 2 + 4 * s * s * r * u * u) - a) / (u * u)
    data = {
        "n": n, "s": s, "u": u,
        "projection_error": float(np.linalg.norm(p @ p - p)),
        "diagonal_error": float(np.linalg.norm(np.diag(p) - r)),
        "orthogonal_pairs_error": float(np.max(np.abs(np.sum(vp.conj() * vm, axis=0)))),
        "reference_identity_error": float(np.linalg.norm(x.sum(0) - marginal)),
        "input_norm_gap": in_gap,
        "input_norm_gap_expected": 2 * n * u * u,
        "ratio_actual": out_gap / in_gap,
        "ratio_formula": float(formula),
        "limit": float(s * (1 + (n - 1) * s) / (1 - (n - 3) * s)),
        "normalized_positive_gap": in_gap / (2 * norm),
    }
    assert abs(in_gap - 2 * n * u * u) < 1e-9
    assert abs(out_gap / in_gap - formula) < 1e-8
    if bell:
        d = round(np.sqrt(n))
        assert d * d == n
        phi = bell_family(d)
        rho = sum(np.kron(plus[i], phi[i]) for i in range(n)) / norm
        sigma = sum(np.kron(minus[i], phi[i]) for i in range(n)) / norm
        delta = rho - sigma
        refdim = (2 * n + 2) * d
        ref = np.trace(delta.reshape(refdim, d, refdim, d), axis1=1, axis2=3)
        expected_ref = np.kron(marginal, np.eye(d) / d) / norm
        actual_output = ((1 + s) / d) * np.kron(ref, np.eye(d)) - s * delta
        expected_output = sum(np.kron(y[i], phi[i]) for i in range(n)) / norm
        encoded_gap = trace_norm(delta) - trace_norm(ref)
        encoded_ratio = (trace_norm(actual_output) - trace_norm(ref)) / encoded_gap
        data.update({
            "rho_trace": float(np.trace(rho).real),
            "sigma_trace": float(np.trace(sigma).real),
            "rho_min_eigenvalue": float(np.linalg.eigvalsh(rho).min()),
            "sigma_min_eigenvalue": float(np.linalg.eigvalsh(sigma).min()),
            "bell_reference_error": float(np.linalg.norm(ref - expected_ref)),
            "bell_output_error": float(np.linalg.norm(actual_output - expected_output)),
            "bell_ratio": encoded_ratio,
        })
        assert np.linalg.norm(ref - expected_ref) < 1e-10
        assert np.linalg.norm(actual_output - expected_output) < 1e-10
        assert abs(encoded_ratio - formula) < 1e-8
    return data


if __name__ == "__main__":
    rows = []
    for n in (3, 4, 5, 9):
        for fraction in (0.0, 0.7, 1.0):
            for u in (0.25, 0.05):
                rows.append(validate(n, fraction / (n - 1), u,
                                     bell=n in (4, 9) and u == 0.25))
    print(json.dumps({"status": "all assertions passed", "cases": rows}, indent=2))
