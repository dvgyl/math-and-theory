#!/usr/bin/env python3
"""Exhaustive check of the loose-cycle Berge-path saturation witnesses.

For m >= 5 put d = m - 2.  The witness W(d, t) consists of t disjoint loose
d-cycles and two isolated vertices on n = 2td + 2 vertices: in copy j the
hyperedges are {2dj+i, 2dj+((i+1) mod d), 2dj+d+i} for 0 <= i < d.

A Berge path of length L consists of distinct vertices v_0, ..., v_L and
distinct hyperedges e_1, ..., e_L with {v_(i-1), v_i} contained in e_i; a
Berge-P_m is a Berge path of length m - 1.  The script checks by exhaustive
depth-first search that W(d, t) has no Berge path of length m - 1 and that
adding any absent 3-set creates one, and it compares the edge count with the
value ceil((n - floor(n/b))/2), b = 2a + 1, a = (3+r)2^s - 5 for m = 4s + r,
1 <= r <= 4, conjectured in Conjecture 2.4 of arXiv:1710.03735v1.
Standard library only.  Usage: python3 check_witness.py [--json]
"""
from itertools import combinations
import json
import sys


def witness(d, t):
    n = 2 * t * d + 2
    edges = []
    for j in range(t):
        base = 2 * d * j
        for i in range(d):
            edges.append(frozenset({base + i, base + (i + 1) % d, base + d + i}))
    return n, edges


def a_value(m):
    s = (m - 1) // 4
    r = m - 4 * s
    return (3 + r) * 2 ** s - 5


def conjectured(m, n):
    b = 2 * a_value(m) + 1
    return -(-(n - n // b) // 2)


def has_path(n, edges, length):
    """Return a Berge path (vertices, edge indices) of the given length, or None."""
    incident = [[] for _ in range(n)]
    for k, e in enumerate(edges):
        for v in e:
            incident[v].append(k)
    used_v = [False] * n
    used_e = [False] * len(edges)
    verts, eidx = [], []

    def extend(v):
        if len(eidx) == length:
            return True
        for k in incident[v]:
            if used_e[k]:
                continue
            used_e[k] = True
            eidx.append(k)
            for w in edges[k]:
                if not used_v[w]:
                    used_v[w] = True
                    verts.append(w)
                    if extend(w):
                        return True
                    verts.pop()
                    used_v[w] = False
            eidx.pop()
            used_e[k] = False
        return False

    for v in range(n):
        used_v[v] = True
        verts.append(v)
        if extend(v):
            return list(verts), list(eidx)
        verts.pop()
        used_v[v] = False
    return None


def check_path(edges, verts, eidx, length):
    assert len(verts) == length + 1 and len(eidx) == length
    assert len(set(verts)) == len(verts) and len(set(eidx)) == len(eidx)
    assert len({edges[k] for k in eidx}) == length
    for i, k in enumerate(eidx):
        assert verts[i] in edges[k] and verts[i + 1] in edges[k]


def check(m, t):
    d = m - 2
    n, edges = witness(d, t)
    length = m - 1
    assert all(len(e) == 3 for e in edges) and len(set(edges)) == len(edges)
    assert has_path(n, edges, length) is None, "witness contains a Berge path"
    present = set(edges)
    absent = 0
    for triple in combinations(range(n), 3):
        f = frozenset(triple)
        if f in present:
            continue
        absent += 1
        augmented = edges + [f]
        found = has_path(n, augmented, length)
        assert found is not None, f"adding {sorted(f)} creates no Berge path"
        verts, eidx = found
        check_path(augmented, verts, eidx, length)
        assert len(edges) in eidx, "a new path must use the added edge"
    a = a_value(m)
    b = 2 * a + 1
    return {
        "m": m, "d": d, "t": t, "n": n, "edges": len(edges), "absent_triples": absent,
        "a": a, "b": b, "in_exceptional_range": b < n < 2 * b,
        "conjectured_value": conjectured(m, n), "saturated": True,
    }


def main():
    results = [check(10, 2), check(10, 3), check(11, 3)]
    for r in results:
        assert r["edges"] == r["conjectured_value"] - 1 and r["in_exceptional_range"]
    out = {"verified": True, "cases": results}
    if "--json" in sys.argv:
        print(json.dumps(out, indent=2))
    else:
        for r in results:
            print(f"m={r['m']} n={r['n']}: saturated with {r['edges']} edges; "
                  f"{r['absent_triples']} absent triples checked; conjectured value {r['conjectured_value']}")


if __name__ == "__main__":
    main()
