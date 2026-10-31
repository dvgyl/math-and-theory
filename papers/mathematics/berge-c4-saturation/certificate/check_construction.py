#!/usr/bin/env python3
"""Standard-library check of the upper construction and of the small witnesses.

Usage: python3 certificate/check_construction.py [--max-n N] [--json OUT]

For every 9 <= n <= N (default 24) the script builds the hypergraph of Section 3 of the
manuscript (the base on n0 = 9 + (n - 9) mod 4 vertices glued at vertex 0 to (n - n0)/4
blocks), checks that it is simple and three-uniform with ceil((3n - 9)/4) hyperedges, that
no four distinct hyperedges carry a Berge four-cycle, and that every absent triple creates
one.  It checks the cone witnesses for n = 3, ..., 8 in the same way and evaluates the
lower bound of Theorem 1.  The Berge-C4 test assigns four distinct vertices to the four
cyclic intersections of four distinct hyperedges; it does not use the path criterion.
"""
import argparse
import itertools
import json
import math

BASES = {
    9: [(0, 1, 2), (0, 1, 3), (0, 2, 4), (0, 5, 6), (1, 7, 8)],
    10: [(0, 1, 2), (0, 1, 3), (0, 1, 4), (0, 2, 5), (0, 6, 7), (1, 8, 9)],
    11: [(0, 1, 2), (0, 1, 3), (0, 2, 4), (0, 5, 6), (1, 7, 8), (2, 9, 10)],
    12: [(0, 1, 2), (0, 1, 3), (0, 1, 4), (0, 2, 5), (0, 6, 7), (1, 8, 9), (2, 10, 11)],
}
SMALL = {
    3: [(0, 1, 2)],
    4: [(0, 1, 2), (0, 1, 3), (0, 2, 3)],
    5: [(0, 1, 2), (0, 1, 3), (0, 2, 4)],
    6: [(0, 1, 2), (0, 1, 3), (0, 2, 4), (0, 2, 5)],
    7: [(0, 1, 2), (0, 3, 4), (0, 3, 5), (0, 4, 6)],
    8: [(0, 1, 2), (0, 3, 4), (0, 3, 5), (0, 4, 6), (0, 4, 7)],
}
EXACT = [0, 0, 0, 1, 3, 3, 4, 4, 5, 5, 6, 6, 7, 8]


def construction(n):
    n0 = 9 + (n - 9) % 4
    edges = list(BASES[n0])
    for j in range((n - n0) // 4):
        b, c, x, y = (n0 + 4 * j + k for k in range(4))
        edges += [(0, b, c), (0, b, x), (0, c, y)]
    return edges


def cyclic(edges, order):
    common = [edges[order[i]] & edges[order[(i + 1) % 4]] for i in range(4)]
    return any(len(set(v)) == 4 for v in itertools.product(*common))


def has_c4(edges, must=None):
    """Some four distinct hyperedges (one equal to index `must`, if given) carry a C4."""
    indices = range(len(edges))
    for quad in itertools.combinations(indices, 4):
        if must is not None and must not in quad:
            continue
        a, b, c, d = quad
        if any(cyclic(edges, o) for o in ((a, b, c, d), (a, b, d, c), (a, c, b, d))):
            return True
    return False


def check(n, triples):
    edges = [frozenset(t) for t in triples]
    assert all(len(e) == 3 and max(e) < n for e in edges), "not three-uniform on range(n)"
    assert len(set(edges)) == len(edges), "repeated hyperedge"
    assert not has_c4(edges), "contains a Berge-C4"
    present = set(edges)
    by_vertex = {v: [i for i, e in enumerate(edges) if v in e] for v in range(n)}
    missing = 0
    for f in itertools.combinations(range(n), 3):
        f = frozenset(f)
        if f in present:
            continue
        missing += 1
        # Only hyperedges meeting f or meeting a hyperedge through f can join a cycle with f;
        # restricting to them keeps the exhaustive test fast without changing its outcome.
        near = {i for v in f for i in by_vertex[v]}
        near |= {i for j in list(near) for v in edges[j] for i in by_vertex[v]}
        local = [edges[i] for i in sorted(near)] + [f]
        assert has_c4(local, must=len(local) - 1), f"absent triple {sorted(f)} is safe"
    return {"n": n, "edges": len(edges), "missing_triples_checked": missing}


def lower_bound(n):
    """max(ceil((n-1)/2), ceil((5n-3623)/8), ceil((5n+89)/8 - sqrt(270n+1891)/4))."""
    a = (n - 1 + 1) // 2
    b = -((3623 - 5 * n) // 8)
    # smallest integer m with 8m >= 5n + 89 - 2 sqrt(270n + 1891), exactly
    m = 0
    while (5 * n + 89 - 8 * m) > 0 and (5 * n + 89 - 8 * m) ** 2 > 4 * (270 * n + 1891):
        m += 1
    return max(a, b, m)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-n", type=int, default=24)
    parser.add_argument("--json", action="store_true", help="print a JSON record")
    args = parser.parse_args()
    upper = []
    for n in range(9, args.max_n + 1):
        row = check(n, construction(n))
        assert row["edges"] == (3 * n - 6) // 4 == math.ceil((3 * n - 9) / 4)
        upper.append(row)
    small = [check(n, t) for n, t in SMALL.items()]
    assert [r["edges"] for r in small] == EXACT[3:9]
    for n in range(4, len(EXACT)):
        assert lower_bound(n) <= EXACT[n]
    samples = {str(n): {"lower": lower_bound(n), "upper": (3 * n - 6) // 4}
               for n in (13, 100, 10**4, 10**6)}
    result = {"verified": True, "upper_construction": upper, "small_witnesses": small,
              "bound_samples": samples}
    if args.json:
        print(json.dumps(result, indent=2))
    else:
        print(f"Checked the construction for n = 9..{args.max_n} and the witnesses for n = 3..8.")


if __name__ == "__main__":
    main()
