#!/usr/bin/env python3
"""Independent complete diameter-four / at-most-five-boundary verifier.

Uses only the Python standard library. It does not read the primary C++
program, its metric lists, or its survivors. Integer metric arrays on five
designated boundary vertices are generated from scratch, modulo exact S_5
orbits. Every admissible interior profile and every subset is considered.
Actual graph distances are recomputed by BFS before any stability test.

The finite representation is justified in the accompanying research paper:
the CEJZ boundary is contained in the harmonic boundary; distances to a set
containing it give an isometric l-infinity embedding. An interior vertex in
a diameter-four graph has all five coordinates in {1,2,3}, and each of its
coordinates has a tight partner f_i+f_j=M_ij. Adjacency is forced by profile
distance one. Padding the designated boundary to five covers boundary <=5.

Run: python3 verify_diameter4_frames_independent.py [--output DIRECTORY]
"""

from argparse import ArgumentParser
from collections import Counter, deque
from itertools import combinations, permutations, product
import json
from pathlib import Path
from time import monotonic


PAIRS = tuple(combinations(range(5), 2))
PAIR_INDEX = {pair: i for i, pair in enumerate(PAIRS)}
PERMUTED_INDICES = tuple(
    tuple(PAIR_INDEX[tuple(sorted((p[i], p[j])))] for i, j in PAIRS)
    for p in permutations(range(5))
)
TRIANGLES = tuple(combinations(range(5), 3))
PROFILE_POOL = tuple(product((1, 2, 3), repeat=5))


def matrix_of(values):
    m = [[0] * 5 for _ in range(5)]
    for (i, j), value in zip(PAIRS, values):
        m[i][j] = m[j][i] = value
    return m


def metric(values):
    m = matrix_of(values)
    for i, j, k in TRIANGLES:
        x, y, z = m[i][j], m[i][k], m[j][k]
        if 2 * max(x, y, z) > x + y + z:
            return None
    return m


def profiles(m):
    result = []
    for f in PROFILE_POOL:
        if any(not (abs(f[i] - f[j]) <= m[i][j] <= f[i] + f[j])
               for i, j in PAIRS):
            continue
        if any(not any(j != i and f[i] + f[j] == m[i][j]
                       for j in range(5)) for i in range(5)):
            continue
        result.append(f)
    return result


def distances(adjacency):
    result = []
    n = len(adjacency)
    for source in range(n):
        d = [-1] * n
        d[source] = 0
        queue = deque([source])
        while queue:
            u = queue.popleft()
            for v in adjacency[u]:
                if d[v] < 0:
                    d[v] = d[u] + 1
                    queue.append(v)
        if -1 in d:
            return None
        result.append(d)
    return result


def cut_vertices(adjacency):
    n = len(adjacency)
    cuts = []
    for deleted in range(n):
        start = 0 if deleted != 0 else 1
        visited = {deleted, start}
        queue = deque([start])
        while queue:
            u = queue.popleft()
            for v in adjacency[u]:
                if v not in visited:
                    visited.add(v)
                    queue.append(v)
        if len(visited) < n:
            cuts.append(deleted)
    return cuts


def encode_graph6(adjacency):
    n = len(adjacency)
    assert n <= 62
    bits = [int(i in adjacency[j]) for j in range(1, n) for i in range(j)]
    bits.extend([0] * ((-len(bits)) % 6))
    return chr(n + 63) + ''.join(chr(63 + sum(bits[k + t] << (5 - t)
                           for t in range(6))) for k in range(0, len(bits), 6))


def main(output):
    start = monotonic()
    seen_metrics = set()
    orbit_stats, labelled_stats = Counter(), Counter()
    profile_count_histogram, survivors = Counter(), []
    max_profiles = 0

    def count(key, weight):
        orbit_stats[key] += 1
        labelled_stats[key] += weight

    for values in product((1, 2, 3, 4), repeat=10):
        if 4 not in values or values in seen_metrics:
            continue
        m = metric(values)
        if m is None:
            continue
        orbit = {tuple(values[i] for i in indices)
                 for indices in PERMUTED_INDICES}
        seen_metrics.update(orbit)
        weight = len(orbit)
        count('metrics', weight)
        interior = profiles(m)
        q = len(interior)
        max_profiles = max(max_profiles, q)
        profile_count_histogram[q] += weight
        all_profiles = [tuple(row) for row in m] + interior
        profile_distances = [
            [max(abs(a - b) for a, b in zip(f, g)) for g in all_profiles]
            for f in all_profiles
        ]
        for mask in range(1 << q):
            count('subsets', weight)
            selected = list(range(5)) + [5 + j for j in range(q) if mask >> j & 1]
            n = len(selected)
            adjacency = [
                [j for j, s in enumerate(selected)
                 if i != j and profile_distances[r][s] == 1]
                for i, r in enumerate(selected)
            ]
            if any(len(row) < 2 for row in adjacency):
                count('minimum_degree_rejections', weight)
                continue
            d = distances(adjacency)
            if d is None:
                count('disconnected_rejections', weight)
                continue
            if any(d[i][j] != profile_distances[r][s]
                   for i, r in enumerate(selected)
                   for j, s in enumerate(selected)):
                count('metric_rejections', weight)
                continue
            assert max(map(max, d)) == 4
            beta = [max(sum(d[u][t] - d[v][t] for v in adjacency[u])
                        for t in range(n)) for u in range(n)]
            if any(value > 0 for value in beta[5:]):
                count('interior_boundary_rejections', weight)
                continue
            count('nonboundary_interior_survivors', weight)
            boundary = [i for i, value in enumerate(beta) if value > 0]
            assert len(boundary) <= 5
            cuts = cut_vertices(adjacency)
            count('cut_vertex_survivors' if cuts else 'two_connected_survivors', weight)
            survivors.append({
                'boundary_metric_upper_triangle': values,
                'metric_orbit_size': weight,
                'interior_profiles': [interior[j] for j in range(q) if mask >> j & 1],
                'edges': [[i, j] for i, row in enumerate(adjacency) for j in row if i < j],
                'graph6': encode_graph6(adjacency),
                'beta': beta,
                'boundary': boundary,
                'cut_vertices': cuts,
            })

        if orbit_stats['metrics'] % 250 == 0:
            print(f"{orbit_stats['metrics']} metric orbits, "
                  f"{orbit_stats['subsets']} subsets, "
                  f"{monotonic() - start:.1f}s", flush=True)

    assert len(seen_metrics) == labelled_stats['metrics']
    assert max_profiles == 12
    assert labelled_stats['metrics'] == 205150
    assert labelled_stats['subsets'] == 15078388
    assert labelled_stats['two_connected_survivors'] == 0
    assert labelled_stats['nonboundary_interior_survivors'] == 115
    output.mkdir(parents=True, exist_ok=True)
    summary = {
        'claim': 'No finite simple 2-connected graph of diameter four has at most five harmonic boundary vertices.',
        'method': 'Independent standard-library Python metric-orbit enumeration and fresh all-pairs BFS.',
        'assumptions': 'The proved CEJZ-boundary frame theorem; no graph-order cutoff or degree-three obstruction is used.',
        'metric_pair_order': PAIRS,
        'orbit_counts': dict(orbit_stats),
        'labelled_counts': dict(labelled_stats),
        'maximum_admissible_interior_profiles': max_profiles,
        'labelled_metric_profile_count_histogram': dict(sorted(profile_count_histogram.items())),
        'seconds': round(monotonic() - start, 3),
        'survivors': survivors,
    }
    destination = output / 'diameter4_independent_verification.json'
    destination.write_text(json.dumps(summary, indent=2) + '\n')
    print(json.dumps({key: value for key, value in summary.items() if key != 'survivors'}, indent=2))
    print(f"Saved {destination}")


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=Path(__file__).resolve().parent)
    main(parser.parse_args().output)
