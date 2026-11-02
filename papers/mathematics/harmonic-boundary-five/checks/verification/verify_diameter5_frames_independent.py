#!/usr/bin/env python3
"""Independent diameter-five frame exclusion, using exact metric orbits.

Pure Python standard library. This program independently generates every
five-point integral boundary metric of diameter five up to relabelling, then
every admissible interior profile and every possible subset surviving a
necessary degree filter. Every surviving graph is checked using fresh BFS.

The lower degree bound four for interior vertices uses the proved theorem:
a non-cut nonboundary vertex of degree three forces at least six boundary
vertices; a degree-two vertex on a cycle is boundary. Consequently this is
an exhaustive exclusion for 2-connected graphs, not a census of cut graphs.

Run from any directory: python3 verify_diameter5_frames_independent.py
"""

from argparse import ArgumentParser
from collections import Counter
from itertools import product
import json
from pathlib import Path
from time import monotonic

from verify_diameter4_frames_independent import (
    PAIRS, PERMUTED_INDICES, metric, distances, cut_vertices, encode_graph6,
)


def profile_list(m, diameter):
    result = []
    for f in product(range(1, diameter), repeat=5):
        if any(not (abs(f[i] - f[j]) <= m[i][j] <= f[i] + f[j])
               for i, j in PAIRS):
            continue
        if any(not any(j != i and f[i] + f[j] == m[i][j]
                       for j in range(5)) for i in range(5)):
            continue
        result.append(f)
    return result


def main(output, diameter):
    start = monotonic()
    seen_metrics = set()
    counts, weighted = Counter(), Counter()
    sizes, pruned_sizes = Counter(), Counter()
    survivors = []

    def count(key, weight, amount=1):
        counts[key] += amount
        weighted[key] += amount * weight

    # Every diameter-D metric can be relabelled so that M_01=D.
    # Store only orbit elements with this property, but retain the size of
    # the whole orbit as the labelled weight.
    for tail in product(range(1, diameter + 1), repeat=9):
        values = (diameter,) + tail
        if values in seen_metrics:
            continue
        m = metric(values)
        if m is None:
            continue
        orbit = {tuple(values[i] for i in indices)
                 for indices in PERMUTED_INDICES}
        seen_metrics.update(v for v in orbit if v[0] == diameter)
        weight = len(orbit)
        count('metric_orbits', weight)
        interior = profile_list(m, diameter)
        q = len(interior)
        sizes[q] += 1
        count('unpruned_profile_subsets', weight, 1 << q)
        profiles = [tuple(row) for row in m] + interior
        pd = [[max(abs(a - b) for a, b in zip(f, g)) for g in profiles]
              for f in profiles]
        neighbor_masks = [sum(1 << j for j, d in enumerate(row) if d == 1)
                          for row in pd]
        keep = (1 << len(profiles)) - 1

        # Delete profiles which could not possibly have degree >=4 in a
        # candidate induced graph. No feasible 2-connected graph is lost.
        while True:
            bad = sum(1 << i for i in range(5, len(profiles))
                      if keep >> i & 1 and (neighbor_masks[i] & keep).bit_count() < 4)
            if not bad:
                break
            keep &= ~bad
        if any((neighbor_masks[i] & keep).bit_count() < 2 for i in range(5)):
            count('metric_rejected_by_ambient_degree', weight)
            continue
        indices = [i for i in range(len(profiles)) if keep >> i & 1]
        q = len(indices) - 5
        pruned_sizes[q] += 1
        pd = [[pd[i][j] for j in indices] for i in indices]
        profiles = [profiles[i] for i in indices]
        neighbor_masks = [sum(1 << j for j, d in enumerate(row) if d == 1)
                          for row in pd]

        for subset in range(1 << q):
            count('examined_profile_subsets', weight)
            present = 31 | (subset << 5)
            if any((neighbor_masks[i] & present).bit_count() < 2 for i in range(5)):
                count('boundary_degree_rejections', weight)
                continue
            active = subset
            feasible = True
            while active:
                bit = active & -active
                i = bit.bit_length() + 4
                if (neighbor_masks[i] & present).bit_count() < 4:
                    feasible = False
                    break
                active -= bit
            if not feasible:
                count('interior_degree_rejections', weight)
                continue
            selected = [i for i in range(len(profiles)) if present >> i & 1]
            adjacency = [[j for j, v in enumerate(selected) if pd[u][v] == 1]
                         for u in selected]
            d = distances(adjacency)
            if d is None:
                count('disconnected_rejections', weight)
                continue
            if any(d[i][j] != pd[u][v] for i, u in enumerate(selected)
                   for j, v in enumerate(selected)):
                count('metric_rejections', weight)
                continue
            assert max(map(max, d)) == diameter
            n = len(adjacency)
            beta = [max(sum(d[u][t] - d[v][t] for v in adjacency[u])
                        for t in range(n)) for u in range(n)]
            if any(value > 0 for value in beta[5:]):
                count('interior_boundary_rejections', weight)
                continue
            count('score_survivors', weight)
            cuts = cut_vertices(adjacency)
            count('cut_vertex_survivors' if cuts else 'two_connected_survivors', weight)
            survivors.append({
                'boundary_metric_upper_triangle': values,
                'metric_orbit_size': weight,
                'interior_profiles': [profiles[i] for i in selected if i >= 5],
                'graph6': encode_graph6(adjacency),
                'beta': beta,
                'cut_vertices': cuts,
            })
        if counts['metric_orbits'] % 1000 == 0:
            print(f"{counts['metric_orbits']} metric orbits, "
                  f"{counts['examined_profile_subsets']} examined subsets, "
                  f"{monotonic() - start:.1f}s", flush=True)

    if diameter == 5:
        assert counts['metric_orbits'] == 11962
        assert weighted['metric_orbits'] == 1195805
        assert counts['unpruned_profile_subsets'] == 17177804
        assert max(sizes) == 20
    assert counts['two_connected_survivors'] == 0
    summary = {
        'claim': f'No finite simple 2-connected graph of diameter {diameter} has at most five harmonic boundary vertices.',
        'method': 'Independent exact five-point metric orbits, admissible profile subsets, integer BFS and boundary scores.',
        'theoretical_inputs': [
            'CEJZ boundary is contained in the harmonic boundary.',
            'Distances to any set containing the CEJZ boundary give an isometric l-infinity embedding.',
            'Each interior distance coordinate has a tight partner among the boundary coordinates.',
            'In a 2-connected graph with at most five harmonic boundary vertices every interior vertex has degree at least four.',
        ],
        'orbit_counts': dict(counts),
        'labelled_counts': dict(weighted),
        'unpruned_profile_count_histogram': dict(sorted(sizes.items())),
        'after_ambient_degree_pruning_profile_count_histogram': dict(sorted(pruned_sizes.items())),
        'seconds': round(monotonic() - start, 3),
        'survivors': survivors,
    }
    output.mkdir(parents=True, exist_ok=True)
    path = output / f'diameter{diameter}_independent_verification.json'
    path.write_text(json.dumps(summary, indent=2) + '\n')
    print(json.dumps({k: v for k, v in summary.items() if k != 'survivors'}, indent=2))
    print(f'Saved {path}')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=Path(__file__).resolve().parent)
    parser.add_argument('--diameter', type=int, default=5)
    args = parser.parse_args()
    main(args.output, args.diameter)
