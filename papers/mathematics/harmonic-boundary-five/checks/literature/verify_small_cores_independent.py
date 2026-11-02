#!/usr/bin/env python3
"""Independently verify all diameter <= 2, b <= 5, 2-connected cores.

Only the Python standard library is used. This enumerates every labeled graph
on 3, 4, 5, and 6 vertices, not the NetworkX atlas. Isomorphism comparison uses
exhaustive degree-compatible permutations, not hashes. The theorem bounding
core order by 6 is conventional mathematics; this checks the remaining finite
classification and all stability values in the supplied JSON file.
"""
import collections
import itertools
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def connected(adj, deleted=-1):
    n = len(adj)
    unseen = ((1 << n) - 1) ^ (1 << deleted if deleted >= 0 else 0)
    start = unseen & -unseen
    unseen ^= start
    frontier = start
    while frontier:
        bit = frontier & -frontier
        frontier ^= bit
        vertex = bit.bit_length() - 1
        new = adj[vertex] & unseen
        unseen ^= new
        frontier |= new
    return unseen == 0


def distances(adj):
    n = len(adj)
    d = [[n] * n for _ in range(n)]
    for root in range(n):
        d[root][root] = 0
        queue = [root]
        for x in queue:
            for y in range(n):
                if (adj[x] >> y) & 1 and d[root][y] == n:
                    d[root][y] = d[root][x] + 1
                    queue.append(y)
    return d


def stability(adj, d):
    n = len(adj)
    return [max(sum(d[x][y] - d[z][y] for z in range(n)
                    if (adj[x] >> z) & 1) for y in range(n))
            for x in range(n)]


def isomorphic(adj, target):
    n = len(adj)
    d1 = [x.bit_count() for x in adj]
    d2 = [x.bit_count() for x in target]
    classes1 = collections.defaultdict(list)
    classes2 = collections.defaultdict(list)
    for x in range(n):
        classes1[d1[x]].append(x)
        classes2[d2[x]].append(x)
    if sorted(d1) != sorted(d2):
        return False
    degrees = sorted(classes1)
    for assignments in itertools.product(
            *(itertools.permutations(classes2[deg]) for deg in degrees)):
        perm = [None] * n
        for deg, images in zip(degrees, assignments):
            for x, image in zip(classes1[deg], images):
                perm[x] = image
        if all(((adj[x] >> y) & 1) == ((target[perm[x]] >> perm[y]) & 1)
               for x in range(n) for y in range(x)):
            return True
    return False


def main():
    data = json.loads((ROOT / 'experiments/small_biconnected_cores.json').read_text())
    seeds = []
    buckets = collections.defaultdict(list)
    for item in data:
        n = item['n']
        adj = [0] * n
        for u, v in item['edges']:
            adj[u] |= 1 << v
            adj[v] |= 1 << u
        d = distances(adj)
        beta = stability(adj, d)
        assert beta == item['beta']
        assert all(connected(adj, x) for x in range(n))
        assert max(map(max, d)) <= 2
        assert sum(v > 0 for v in beta) == item['boundary_size'] <= 5
        key = (n, tuple(sorted(x.bit_count() for x in adj)))
        buckets[key].append((item['id'], adj))
        seeds.append(adj)
    for i, a in enumerate(seeds):
        for b in seeds[i+1:]:
            if len(a) == len(b):
                assert not isomorphic(a, b)

    counts = collections.Counter()
    hits = collections.Counter()
    checked = 0
    for n in range(3, 7):
        edges = list(itertools.combinations(range(n), 2))
        for mask in range(1 << len(edges)):
            checked += 1
            adj = [0] * n
            for i, (u, v) in enumerate(edges):
                if (mask >> i) & 1:
                    adj[u] |= 1 << v
                    adj[v] |= 1 << u
            if min(x.bit_count() for x in adj) < 2:
                continue
            if not all(connected(adj, x) for x in range(n)):
                continue
            d = distances(adj)
            if max(map(max, d)) > 2:
                continue
            beta = stability(adj, d)
            k = sum(x > 0 for x in beta)
            if k > 5:
                continue
            key = (n, tuple(sorted(x.bit_count() for x in adj)))
            matching = [ident for ident, seed in buckets[key]
                        if isomorphic(adj, seed)]
            assert len(matching) == 1, (n, mask, beta, matching)
            hits[matching[0]] += 1
            counts[f'n{n}_boundary{k}_labeled'] += 1
    assert len(hits) == len(data) == 24
    result = {
        'all_assertions_passed': True,
        'labeled_graphs_checked': checked,
        'cores_found_up_to_isomorphism': len(hits),
        'labeled_counts': dict(sorted(counts.items())),
        'seed_labeled_multiplicities': dict(sorted(hits.items())),
        'scope': 'All labeled simple graphs of orders 3 through 6; pure Python.',
    }
    path = Path(__file__).with_name('small_core_independent_audit.json')
    path.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
