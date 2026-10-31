#!/usr/bin/env python3
"""Exact checks for the Berge-triangle upper saturation spectrum.

Standard library only.  The script
  1. builds the boundary construction J(p, q) with p = floor(n/4) and every paired
     product F(n, p) above the threshold for 8 <= n <= --direct-max, and checks
     freeness, saturation, sizes and product recognition by direct search;
  2. compares, for 8 <= n <= --arith-max, the product sizes in (L_n, E_n] with the
     deficit characterization of Corollary 4 and the formula for W_n;
  3. checks the witness files given on the command line directly.
Vertices are 0-based.  Freeness uses Hall's condition for three edge sets on every vertex
triple; saturation tests, for every absent triple, whether one of its pairs closes a
two-edge Berge path of distinct old edges.
"""
import argparse
import itertools as it
import json
import sys
from pathlib import Path


def E(n):
    return n * n // 8


def L(n):
    return (n - 1) ** 2 // 8 if n >= 1 else 0


def pair_index(edges):
    index = {}
    for k, e in enumerate(edges):
        for a, b in it.combinations(sorted(e), 2):
            index.setdefault((a, b), set()).add(k)
    return index


def pkey(a, b):
    return (a, b) if a < b else (b, a)


def is_free(n, edges):
    index = pair_index(edges)
    for x, y, z in it.combinations(range(n), 3):
        A = index.get((x, y), set())
        B = index.get((y, z), set())
        C = index.get((x, z), set())
        if not (A and B and C):
            continue
        if (len(A | B) >= 2 and len(A | C) >= 2 and len(B | C) >= 2
                and len(A | B | C) >= 3):
            return False
    return True


def closes_path(n, index, triple):
    for a, b in it.combinations(triple, 2):
        for w in range(n):
            if w in (a, b):
                continue
            first = index.get(pkey(a, w), set())
            second = index.get(pkey(w, b), set())
            if first and second and len(first | second) >= 2:
                return True
    return False


def is_saturated(n, edges):
    if not is_free(n, edges):
        return False
    present = {tuple(sorted(e)) for e in edges}
    index = pair_index(edges)
    for triple in it.combinations(range(n), 3):
        if triple not in present and not closes_path(n, index, triple):
            return False
    return True


def verify_product_structure(n, edges, base):
    verts = set(range(n))
    pairs = set()
    for e in edges:
        inside = set(e) & base
        if len(inside) != 1:
            return False
        pairs.add(frozenset(set(e) - base))
    if not base or not pairs or any(len(P) != 2 for P in pairs):
        return False
    covered = set()
    for P in pairs:
        if covered & P:
            return False
        covered |= P
    if covered | base != verts or covered & base:
        return False
    expected = {frozenset(P | {b}) for P in pairs for b in base}
    return expected == {frozenset(e) for e in edges}


def is_paired_product(n, edges):
    """Exact recognition of systems isomorphic to some F(n, p)."""
    if not edges:
        return False
    common = set.intersection(*(set(e) for e in edges))
    for b in common:
        if verify_product_structure(n, edges, {b}):
            return True
    links = {v: [] for v in range(n)}
    for e in edges:
        for v in e:
            links[v].append(frozenset(set(e) - {v}))
    base = set()
    for v in range(n):
        link = links[v]
        if link and all(not (P & Q) for P, Q in it.combinations(link, 2)):
            base.add(v)
    return verify_product_structure(n, edges, base)


def product(n, p):
    pairs = [(2 * i, 2 * i + 1) for i in range(p)]
    return [tuple(sorted((x, y, b))) for x, y in pairs for b in range(2 * p, n)]


def boundary(n, p):
    """J(p, q), q = n - 2p: pairs {2i, 2i+1}, u = 2p, v = 2p + 1, S = {2p+2, ..., n-1}."""
    u, v = 2 * p, 2 * p + 1
    S = range(2 * p + 2, n)
    edges = [(2 * i, 2 * i + 1, z) for i in range(p) for z in S]
    edges += [(2 * i, 2 * i + 1, v) for i in range(1, p)]
    edges.append((0, u, v))
    return [tuple(sorted(e)) for e in edges]


def allowed(n, d):
    r = n % 4
    for j in range(0, d + 2):
        if r == 0 and 2 * j * j == d:
            return True
        if r == 2 and 2 * j * (j + 1) == d:
            return True
        if r in (1, 3) and j * (j + 1) // 2 == d:
            return True
    return False


def product_sizes(n):
    return {p * (n - 2 * p) for p in range(1, (n + 1) // 2) if 2 * p < n}


def check_arithmetic(max_n):
    for n in range(8, max_n + 1):
        sizes = product_sizes(n)
        width = E(n) - L(n)
        if width != n // 4 + (1 if n % 4 == 3 else 0):
            raise AssertionError(f"W_n formula fails at n={n}")
        if max(sizes) != E(n):
            raise AssertionError(f"maximum product size fails at n={n}")
        for d in range(width):
            if ((E(n) - d) in sizes) != allowed(n, d):
                raise AssertionError(f"deficit characterization fails at n={n}, d={d}")
        p = n // 4
        if p * (n - 2 * p - 1) != L(n) or p < 2 or n - 2 * p < 3:
            raise AssertionError(f"boundary size identity fails at n={n}")
    table = {}
    for n in (8, 11, 16, 40, 400):
        window = range(L(n) + 1, E(n) + 1)
        occ = [m for m in window if m in product_sizes(n)]
        table[str(n)] = {"L": L(n), "E": E(n), "occurring": occ,
                         "missing_count": len(window) - len(occ)}
    return {"orders": [8, max_n], "table": table}


def check_constructions(max_n):
    results = []
    for n in range(8, max_n + 1):
        p = n // 4
        J = boundary(n, p)
        if len(set(J)) != len(J) or len(J) != L(n):
            raise AssertionError(f"boundary size fails at n={n}")
        if not is_saturated(n, J):
            raise AssertionError(f"boundary construction not saturated at n={n}")
        if is_paired_product(n, J):
            raise AssertionError(f"boundary construction is a product at n={n}")
        tops = []
        for q in range(1, (n + 1) // 2):
            if 2 * q < n and q * (n - 2 * q) > L(n):
                F = product(n, q)
                if not (is_saturated(n, F) and is_paired_product(n, F)):
                    raise AssertionError(f"F({n},{q}) check fails")
                tops.append(len(F))
        results.append({"n": n, "boundary_edges": len(J), "products_above_threshold": tops})
    return results


def check_witness(path):
    data = json.loads(Path(path).read_text())
    n, raw = data["n"], data["edges"]
    edges = [tuple(sorted(e)) for e in raw]
    if any(len(set(e)) != 3 or min(e) < 0 or max(e) >= n for e in edges):
        raise AssertionError(f"invalid edge in {path}")
    if len(set(edges)) != len(edges):
        raise AssertionError(f"duplicate edge in {path}")
    return {"file": Path(path).name, "n": n, "m": len(edges), "free": is_free(n, edges),
            "saturated": is_saturated(n, edges), "paired_product": is_paired_product(n, edges),
            "L_n": L(n), "E_n": E(n)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("witnesses", nargs="*")
    parser.add_argument("--direct-max", type=int, default=20)
    parser.add_argument("--arith-max", type=int, default=2000)
    args = parser.parse_args()
    report = {
        "arithmetic": check_arithmetic(args.arith_max),
        "constructions": check_constructions(args.direct_max),
        "witnesses": [check_witness(w) for w in args.witnesses],
    }
    for w in report["witnesses"]:
        if not (w["free"] and w["saturated"]):
            raise AssertionError(f"witness check fails: {w['file']}")
    json.dump(report, sys.stdout, indent=1, sort_keys=True)
    print()


if __name__ == "__main__":
    main()
