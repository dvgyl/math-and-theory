#!/usr/bin/env python3
"""Exhaustive standard-library check of the constructions in the manuscript.

Usage: python3 certificate/check_construction.py [--max-n N] [--json]

For every order 7 <= n <= N (default 52) and every edge count m claimed in Theorem 1 the script
builds the hypergraph described in the manuscript and checks directly that it is three-uniform,
simple, contains no Berge-C5 and that every absent triple contains the two ends of a four-edge
Berge path (so adding it creates a Berge-C5).  It also checks every cone size claimed in
Theorem 2 for 5 <= n <= 36, the support construction of Theorem 4 for several unequal
multiplicities, the three-hub classification of Theorem 3 for all multiplicities 0..4, and the
small witnesses for n <= 6.  A Berge path or cycle has distinct core vertices and distinct
hyperedges; further incidences are allowed.
"""
import argparse
import itertools
import json
import sys
import time


def analyse(n, edges):
    """Return (free, good) where good is the set of pairs joined by a four-edge Berge path."""
    edges = [tuple(sorted(e)) for e in edges]
    inc = [[] for _ in range(n)]
    for i, e in enumerate(edges):
        for x in e:
            inc[x].append(i)
    good = set()
    free = True

    def dfs(path, used):
        nonlocal free
        v = path[-1]
        if len(path) == 5:
            a = path[0]
            good.add((min(a, v), max(a, v)))
            for i in inc[v]:
                if i not in used and a in edges[i]:
                    free = False
            return
        for i in inc[v]:
            if i in used:
                continue
            for w in edges[i]:
                if w not in path:
                    dfs(path + [w], used | {i})

    for s in range(n):
        dfs([s], frozenset())
    return free, good


def saturated(n, edges):
    edges = [tuple(sorted(e)) for e in edges]
    if any(len(set(e)) != 3 or not all(0 <= x < n for x in e) for e in edges):
        return False, "not three-uniform"
    if len(set(edges)) != len(edges):
        return False, "repeated hyperedge"
    free, good = analyse(n, edges)
    if not free:
        return False, "contains a Berge-C5"
    present = set(edges)
    for t in itertools.combinations(range(n), 3):
        if t in present:
            continue
        a, b, c = t
        if (a, b) not in good and (a, c) not in good and (b, c) not in good:
            return False, f"adding {t} creates no Berge-C5"
    return True, "saturated"


class Builder:
    def __init__(self):
        self.n = 0
        self.edges = []

    def vertex(self):
        self.n += 1
        return self.n - 1

    def edge(self, *vs):
        self.edges.append(tuple(vs))

    def expand(self, u, v):
        """Loose expansion of the graph edge uv with a new private vertex."""
        leaf = self.vertex()
        self.edge(u, v, leaf)
        return leaf


def interval_family(p, q, t):
    """Section 4: A={a,b,c}, B={a,d,e}, X_j={b,d,x_j}, Y_j={c,e,y_j}, U_i, W_i; root a."""
    h = Builder()
    a, b, c, d, e = (h.vertex() for _ in range(5))
    h.edge(a, b, c)
    h.edge(a, d, e)
    for _ in range(p):
        h.edge(b, d, h.vertex())
    for _ in range(q):
        h.edge(c, e, h.vertex())
    for _ in range(t):
        u, v, w = h.vertex(), h.vertex(), h.vertex()
        h.edge(b, u, v)
        h.edge(e, v, w)
    return h


def cone(link_components, n):
    """Cone with root 0 over a link given as a list of edge lists on fresh labels; pad to n."""
    h = Builder()
    r = h.vertex()
    for comp in link_components:
        labels = {}
        for x, y in comp:
            for z in (x, y):
                if z not in labels:
                    labels[z] = h.vertex()
            h.edge(r, labels[x], labels[y])
    while h.n < n:
        h.vertex()
    return h


def c4():
    return [(0, 1), (1, 2), (2, 3), (3, 0)]


def tree(size):
    """Radius-two tree on `size` >= 7 vertices: centre 0, neighbours 1,2,3 with leaves 4,5,6,
    further leaves attached to neighbour 1."""
    edges = [(0, 1), (0, 2), (0, 3), (1, 4), (2, 5), (3, 6)]
    for k in range(7, size):
        edges.append((1, k))
    return edges


def cone_with(n, trees, extra=None):
    """Cone over `trees` radius-two trees, C4 components and optionally one K2 or isolated
    link vertex, on n vertices in total.  Returns None if the sizes do not fit."""
    rest = n - 1 - (1 if extra == "iso" else 2 if extra == "k2" else 0)
    if trees == 0:
        if rest < 0 or rest % 4:
            return None
        comps = [c4()] * (rest // 4)
    else:
        rest -= 7 * trees
        if rest < 0:
            return None
        comps = [c4()] * (rest // 4)
        sizes = [7] * trees
        sizes[0] += rest % 4
        comps = [tree(s) for s in sizes] + comps
    if extra == "k2":
        comps.append([(0, 1)])
    h = cone(comps, n)
    return h


def expansion(hubs, groups, apex=False):
    """Loose expansion of the bipartite graph with hub part `hubs` (count), one vertex per
    entry of `groups` adjacent to the listed hubs, and optionally an apex adjacent to all hubs."""
    h = Builder()
    hub = [h.vertex() for _ in range(hubs)]
    spokes = {}
    if apex:
        z = h.vertex()
        for i in range(hubs):
            spokes[i] = h.expand(z, hub[i])
    leaves = []
    for nbrs in groups:
        x = h.vertex()
        for i in nbrs:
            leaves.append((i, x, h.expand(hub[i], x)))
    return h, hub, spokes, leaves


def support(cycle_lengths, lam):
    """Theorem 4: support F a disjoint union of cycles, multiplicity lam[k] on its k-th edge."""
    pairs = []
    off = 0
    for length in cycle_lengths:
        for i in range(length):
            pairs.append((off + i, off + (i + 1) % length))
        off += length
    groups = []
    for (i, j), l in zip(pairs, lam):
        groups += [(i, j)] * l
    h, hub, spokes, leaves = expansion(off, groups, apex=True)
    return h, spokes


def support_family(cycle_lengths, n):
    """The Theorem 4 hypergraph on n vertices with all multiplicities at least two."""
    hcount = sum(cycle_lengths)
    total = n - 1 - 2 * hcount
    if total % 3 or total // 3 < 2 * hcount:
        return None
    s = total // 3
    lam = [2] * hcount
    lam[0] += s - 2 * hcount
    return support(cycle_lengths, lam)[0]


def bipartite_family(n):
    """Section 5: H_t (t >= 3) with r in {0,1,2} universal leaves cloned."""
    t, r = (n - 5) // 3, (n - 5) % 3
    h = Builder()
    a, b, c = h.vertex(), h.vertex(), h.vertex()
    ys = [h.vertex() for _ in range(t)]
    for i, y in enumerate(ys):
        h.expand(a, y)
        h.expand(b, y)
        if i < 2:
            h.expand(c, y)
    if r >= 1:
        h.edge(a, ys[0], h.vertex())
    if r == 2:
        h.edge(b, ys[0], h.vertex())
    return h


def three_hub_family(n):
    """Section 6: three hubs, classes of sizes >= 3, plus one incidence and one clone."""
    r = n % 3
    t = (n - 3 - r) // 3
    sizes = [3, 3, t - 6]
    h = Builder()
    hubs = [h.vertex() for _ in range(3)]
    pairs = [(0, 1), (0, 2), (1, 2)]
    z0 = None
    for (u, v), s in zip(pairs, sizes):
        for _ in range(s):
            z = h.vertex()
            if z0 is None:
                z0 = z
            h.expand(hubs[u], z)
            h.expand(hubs[v], z)
    if r >= 1:
        h.edge(hubs[2], z0, h.vertex())
    if r == 2:
        h.edge(hubs[2], z0, h.vertex())
    return h


def ceil_div(a, b):
    return -(-a // b)


def claimed_lower(n):
    low = ceil_div(2 * (n - 1), 3)
    if n >= 14:
        low = min(low, ceil_div(2 * n - 4, 3))
    if n >= 30 or n in (25, 28):
        low = min(low, ceil_div(2 * n - 6, 3))
    if n >= 47 or n in (41, 44):
        low = min(low, ceil_div(2 * n - 8, 3))
    return low


def build(n, m):
    """The construction used in the manuscript for n vertices and m edges."""
    if m == n - 1:
        return cone_with(n, 0), "cone over C4 components"
    if m == n - 2:
        if n == 7:
            return cone_with(n, 0, "k2"), "cone over C4 and K2"
        return cone_with(n, 1), "cone over one radius-two tree and C4 components"
    if ceil_div(2 * (n - 1), 3) <= m <= n - 3:
        t = n - 3 - m
        return interval_family(n - 6 - 3 * t, 1, t), f"interval family t={t}"
    if n >= 47 or n in (41, 44):
        if m == ceil_div(2 * n - 8, 3):
            shape = {0: [4], 1: [3, 3], 2: [5]}[n % 3]
            h = support_family(shape, n)
            if h is not None and len(h.edges) == m:
                return h, f"support {shape}"
    if (n >= 30 and m == ceil_div(2 * n - 6, 3)):
        return three_hub_family(n), "three-hub family"
    if n in (25, 28) and m == ceil_div(2 * n - 6, 3):
        return support_family([3], n), "support [3]"
    if n >= 14 and m == ceil_div(2 * n - 4, 3):
        return bipartite_family(n), "bipartite family"
    raise ValueError(f"no construction for n={n}, m={m}")


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--max-n", type=int, default=52)
    ap.add_argument("--json", action="store_true")
    args = ap.parse_args()
    start = time.monotonic()
    report = {"interval": [], "cones": [], "supports": [], "three_hub_classes": [],
              "small": [], "failures": []}

    def record(n, m, h, label):
        ok, why = saturated(h.n, h.edges)
        entry = {"n": h.n, "m": len(h.edges), "construction": label, "saturated": ok}
        if h.n != n or len(h.edges) != m or not ok:
            report["failures"].append({**entry, "expected": [n, m], "reason": why})
        return entry

    # Theorem 1: every claimed edge count for 7 <= n <= max_n.
    for n in range(7, args.max_n + 1):
        ms = list(range(claimed_lower(n), n - 1))
        if (n - 1) % 4 == 0:
            ms.append(n - 1)
        for m in ms:
            h, label = build(n, m)
            record(n, m, h, label)
        report["interval"].append({"n": n, "lower": claimed_lower(n), "sizes": len(ms)})

    # Theorem 2: every claimed cone size for 5 <= n <= 36.
    for n in range(5, 37):
        if n in (5, 6, 7):
            spec = {5: [4], 6: [4], 7: [5]}[n]
        else:
            spec = list(range(ceil_div(6 * (n - 1), 7), n - 1))
            if (n - 1) % 4 == 0:
                spec.append(n - 1)
        for m in spec:
            k = n - 1 - m
            if k == 0:
                h = cone_with(n, 0)
            elif n <= 7:
                h = cone_with(n, 0, "k2" if (n - 3) % 4 == 0 else "iso")
            else:
                h = cone_with(n, k)
            record(n, m, h, f"cone with {k} trees")
        report["cones"].append({"n": n, "spectrum": [min(spec), max(spec)]})

    # Theorem 4: unequal multiplicities on every admissible support.
    for shape in ([3], [4], [5], [3, 3]):
        hcount = sum(shape)
        for extra in ((0,), (1,), (2,), (1, 1), (3, 1)):
            lam = [2] * hcount
            for i, x in enumerate(extra):
                lam[(2 * i) % hcount] += x
            h, _ = support(shape, lam)
            s = sum(lam)
            e = record(1 + 2 * hcount + 3 * s, hcount + 2 * s, h,
                       f"support {shape} multiplicities {lam}")
            report["supports"].append(e)

    # Theorem 3: three hubs with multiplicities p, q, r in 0..4 (saturated iff all >= 3).
    for p, q, r in itertools.product(range(5), repeat=3):
        if p + q + r == 0:
            continue
        groups = [(0, 1)] * p + [(0, 2)] * q + [(1, 2)] * r
        h, *_ = expansion(3, groups)
        ok, _ = saturated(h.n, h.edges)
        expect = min(p, q, r) >= 3
        report["three_hub_classes"].append({"multiplicities": [p, q, r], "saturated": ok})
        if ok != expect:
            report["failures"].append({"three_hub": [p, q, r], "saturated": ok})

    # Small witnesses: the complete hypergraph for n <= 4 and four-edge examples at n = 5, 6.
    small = {3: [(0, 1, 2)], 4: list(itertools.combinations(range(4), 3)),
             5: [(0, 1, 2), (0, 2, 3), (0, 3, 4), (0, 1, 4)],
             6: [(0, 1, 2), (0, 1, 3), (2, 4, 5), (3, 4, 5)]}
    for n, edges in small.items():
        ok, why = saturated(n, edges)
        report["small"].append({"n": n, "m": len(edges), "saturated": ok})
        if not ok:
            report["failures"].append({"small": n, "reason": why})

    report["passed"] = not report["failures"]
    report["max_n"] = args.max_n
    report["seconds"] = round(time.monotonic() - start, 2)
    if args.json:
        print(json.dumps(report, indent=1))
    else:
        total = sum(x["sizes"] for x in report["interval"])
        print(f"Theorem 1: {total} pairs (n, m) for 7 <= n <= {args.max_n}; "
              f"cones: {len(report['cones'])} orders; supports: {len(report['supports'])}; "
              f"three-hub multiplicities: {len(report['three_hub_classes'])}; "
              f"failures: {len(report['failures'])}; {report['seconds']} s")
    sys.exit(0 if report["passed"] else 1)


if __name__ == "__main__":
    main()
