#!/usr/bin/env python3
"""Independent numerical check of the explicit filter-to-bivector map."""
import json
from pathlib import Path
import numpy as np

rng = np.random.default_rng(20261103)
errors, orthogonality, lengths = [], [], []
for kind in ["interior", "rank_one"]:
    for _ in range(1000):
        T = rng.normal(size=(3, 3))
        c = rng.normal(size=3)
        n = rng.normal(size=3)
        n /= np.linalg.norm(n)
        u = rng.normal(size=3)
        u /= np.linalg.norm(u)
        if kind == "interior":
            u *= rng.uniform(0, 0.999999)
        r = np.sqrt(max(0, 1 - u @ u))
        q = n @ u
        h = np.sqrt(max(0, 1 - q * q))
        if h < 1e-4:
            continue
        N = (n - q / (1 + r) * u) / h
        V = np.cross(n, u) / h
        A = T @ T.T
        d = T @ c
        C = np.array([[0, -d[2], d[1]], [d[2], 0, -d[0]], [-d[1], d[0], 0]])
        reduced = np.trace(A) - N @ A @ N - V @ (A - (c @ c) * np.eye(3)) @ V - 2 * V @ C @ N
        L = r * np.eye(3) + np.outer(u, u) / (1 + r)
        transformed = L @ T + np.outer(u, c)
        value = np.trace(transformed @ transformed.T) - n @ transformed @ transformed.T @ n
        errors.append(abs(value - (1 - q * q) * reduced) / (1 + abs(value)))
        orthogonality.append(abs(N @ V))
        lengths.append(max(abs(N @ N - 1), max(0, V @ V - 1)))

assert max(errors) < 1e-10
assert max(orthogonality) < 1e-10
assert max(lengths) < 1e-10
report = {
    "status": "PASS",
    "cases": len(errors),
    "seed": 20261103,
    "max_relative_identity_error": max(errors),
    "max_orthogonality_error": max(orthogonality),
    "max_feasibility_error": max(lengths),
    "scope": "Independent NumPy test for arbitrary real T,c, including rank-one filters; numerical evidence only, not a proof.",
}
Path(__file__).with_name("filter_reduction_numeric.json").write_text(json.dumps(report, indent=2) + "\n")
print(json.dumps(report, indent=2))
