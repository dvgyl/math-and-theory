#!/usr/bin/env python3
"""Independent integer-only tests of the exact block/cactus theorems.
No third-party dependencies. This is experimental verification, not a proof.
Run: python check_block_theorems.py
"""
from collections import deque
from itertools import combinations
import argparse
import json
import random
from pathlib import Path


def adjacency(n, edges):
    a = [set() for _ in range(n)]
    for u, v in edges:
        assert u != v
        a[u].add(v)
        a[v].add(u)
    return a


def distances(a, source):
    d = [-1] * len(a)
    d[source] = 0
    q = deque([source])
    while q:
        u = q.popleft()
        for v in a[u]:
            if d[v] < 0:
                d[v] = d[u] + 1
                q.append(v)
    return d


def betas(a):
    assert len(a) >= 2
    ds = [distances(a, v) for v in range(len(a))]
    assert all(x >= 0 for row in ds for x in row)
    return [max(len(a[u]) * ds[u][v] - sum(ds[w][v] for w in a[u])
                for v in range(len(a))) for u in range(len(a))]


def blocks(a):
    """Tarjan edge blocks, including singleton bridge blocks."""
    n = len(a)
    disc = [-1] * n
    low = [-1] * n
    parent = [-1] * n
    stack = []
    out = []
    clock = 0

    def dfs(u):
        nonlocal clock
        disc[u] = low[u] = clock
        clock += 1
        for v in sorted(a[u]):
            if disc[v] < 0:
                parent[v] = u
                stack.append((u, v))
                dfs(v)
                low[u] = min(low[u], low[v])
                if low[v] >= disc[u]:
                    component = []
                    while True:
                        edge = stack.pop()
                        component.append(edge)
                        if edge == (u, v):
                            break
                    out.append(component)
            elif v != parent[u] and disc[v] < disc[u]:
                low[u] = min(low[u], disc[v])
                stack.append((u, v))
    dfs(0)
    assert all(d >= 0 for d in disc)
    assert not stack
    return out


def verify(a):
    bg = betas(a)
    bs = blocks(a)
    n = len(a)
    by_vertex = [[] for _ in range(n)]
    sizes = []
    cycle_lengths = []
    block_orders = []
    nonbridge_vertices = set()
    cactus = True
    for edges in bs:
        verts = sorted({u for e in edges for u in e})
        local = {u: i for i, u in enumerate(verts)}
        ba = adjacency(len(verts), [(local[u], local[v]) for u, v in edges])
        bb = betas(ba)
        sizes.append(sum(b > 0 for b in bb))
        block_orders.append(len(verts))
        if len(edges) > 1:
            nonbridge_vertices.update(verts)
        cycle = len(edges) > 1 and len(edges) == len(verts) and all(len(row) == 2 for row in ba)
        if len(edges) > 1 and not cycle:
            cactus = False
        if cycle:
            cycle_lengths.append(len(verts))
        for i, u in enumerate(verts):
            by_vertex[u].append((bb[i], len(ba[i]), len(verts), cycle))
    for u in range(n):
        assert bg[u] == max(beta + deg - len(a[u]) for beta, deg, _, _ in by_vertex[u]), ("block beta", a, u)
    delta = []
    for u in range(n):
        t = len(by_vertex[u])
        if t > 1:
            c = sum(beta > 0 for beta, _, _, _ in by_vertex[u])
            d = 2 * (t - 1) - c + int(bg[u] > 0)
            assert d >= t - 2 >= 0
            delta.append(d)
    k = sum(b > 0 for b in bg)
    assert k == 2 + sum(s - 2 for s in sizes) + sum(delta), ("block budget", a)
    assert sum(len(edges) > 1 for edges in bs) <= k - 2
    assert max(sizes) <= k
    s_count = sum(len(edges) > 1 for edges in bs)
    D = sum(m - q for m, q in zip(block_orders, sizes))
    reduced_order_general = n - sum(len(a[u]) == 2 and u not in nonbridge_vertices for u in range(n))
    assert reduced_order_general <= 2 * k - 2 + 2 * s_count + D
    assert reduced_order_general <= 4 * k - 6 + D
    if D == 0:
        assert reduced_order_general <= 4 * k - 6
    if cactus:
        E = 0
        X = 0
        cyclic = set()
        predicted = set()
        for u in range(n):
            inc = by_vertex[u]
            t = len(inc)
            iscyclic = any(cyc for _, _, _, cyc in inc)
            if iscyclic:
                cyclic.add(u)
            exceptional = len(a[u]) == 3 and any(cyc and m % 2 == 0 for _, _, m, cyc in inc)
            if t > 1:
                X += t - 2
            E += exceptional
            if len(a[u]) == 1 or (len(a[u]) == 2 and iscyclic) or exceptional:
                predicted.add(u)
        assert predicted == {u for u, b in enumerate(bg) if b > 0}, ("cactus membership", a)
        R = sum(m - 2 for m in cycle_lengths)
        assert k == 2 + R + X + E, ("cactus budget", a)
        reduced_order = n - sum(len(a[u]) == 2 and u not in cyclic for u in range(n))
        assert reduced_order <= 4 * k - 6, ("cactus kernel", a)
    return k, cactus


def random_cactus(rng, steps):
    a = adjacency(2, [(0, 1)])
    for _ in range(steps):
        root = rng.randrange(len(a))
        length = rng.choices([2, 3, 4, 5, 6, 7], [5, 3, 2, 1, 1, 1])[0]
        start = len(a)
        for _ in range(length - 1):
            a.append(set())
        verts = [root] + list(range(start, len(a)))
        edges = list(zip(verts, verts[1:]))
        if length > 2:
            edges.append((verts[-1], root))
        for u, v in edges:
            a[u].add(v)
            a[v].add(u)
    return a


def expanded_cubic_tree(k):
    """A trivalent caterpillar expanded to triangles, order 4k-6."""
    assert k >= 2
    if k == 2:
        return adjacency(2, [(0, 1)])
    c = k - 2
    edges = []
    free = []
    for j in range(c):
        p = [3 * j + i for i in range(3)]
        edges.extend([(p[0], p[1]), (p[1], p[2]), (p[2], p[0])])
        used = set()
        if j > 0:
            edges.append((3 * (j - 1) + 1, p[0]))
            used.add(0)
        if j < c - 1:
            used.add(1)
        free.extend(p[i] for i in range(3) if i not in used)
    nxt = 3 * c
    for p in free:
        edges.append((p, nxt))
        nxt += 1
    assert nxt == 4 * k - 6
    return adjacency(nxt, edges)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--max-order', type=int, default=6)
    parser.add_argument('--random-count', type=int, default=300)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    report = {"method": "exact integer arithmetic; independent BFS and Tarjan implementations", "exhaustive_labelled_connected": {}, "seed": 20261101}
    for n in range(2, args.max_order + 1):
        pairs = list(combinations(range(n), 2))
        count = 0
        cactus_count = 0
        five_count = 0
        for mask in range(1 << len(pairs)):
            if mask.bit_count() < n - 1:
                continue
            a = adjacency(n, [e for i, e in enumerate(pairs) if mask & (1 << i)])
            if any(d < 0 for d in distances(a, 0)):
                continue
            k, iscactus = verify(a)
            count += 1
            cactus_count += iscactus
            five_count += k == 5
        report['exhaustive_labelled_connected'][n] = {"connected": count, "cacti": cactus_count, "five_boundary": five_count}
    rng = random.Random(report['seed'])
    for _ in range(args.random_count):
        n = rng.randrange(7, 31)
        edges = [(i, rng.randrange(i)) for i in range(1, n)]
        existing = {tuple(sorted(e)) for e in edges}
        p = rng.random() * 0.4
        edges += [e for e in combinations(range(n), 2) if e not in existing and rng.random() < p]
        verify(adjacency(n, edges))
        verify(random_cactus(rng, rng.randrange(2, 16)))
    report['random_connected'] = args.random_count
    report['random_cacti'] = args.random_count
    report['sharp_examples'] = []
    for k in range(2, 21):
        a = expanded_cubic_tree(k)
        computed, iscactus = verify(a)
        assert computed == k and iscactus and len(a) == 4 * k - 6
        report['sharp_examples'].append({"boundary": k, "vertices": len(a)})
    report['status'] = 'all checks passed'
    rendered = json.dumps(report, indent=2)
    if args.output:
        args.output.write_text(rendered + '\n')
    print(rendered)

if __name__ == '__main__':
    main()
