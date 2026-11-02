#!/usr/bin/env python3
"""Independently exclude all 15 surviving capped-cone metrics by full BFS.

This does not trust either local solver's rejection decisions. Its input is
the explicit positive survivor list; for each such metric it enumerates all
admissible full interior profiles and all subsets, requiring only minimum
degree two before recomputing all graph distances and harmonic scores.
No degree-three theorem or chordal assumption is used in this final check.
"""

from argparse import ArgumentParser
from collections import Counter
import json
from pathlib import Path

from verify_diameter4_frames_independent import matrix_of, distances, cut_vertices, PERMUTED_INDICES
from verify_diameter5_frames_independent import profile_list


def main(source, output):
    hits = json.loads(source.read_text())['hits']
    assert len(hits) == 15
    rows = []
    metric_orbits = set()
    for hit in hits:
        assert max(hit['twice_nonpendant_weights']) <= 3
        values = tuple(hit['metric'])
        m = matrix_of(values)
        diameter = max(values)
        assert diameter in (3, 4)
        metric_orbits.add(min(tuple(values[i] for i in p) for p in PERMUTED_INDICES))
        interior = profile_list(m, diameter)
        ps = [tuple(row) for row in m] + interior
        pd = [[max(abs(a - b) for a, b in zip(f, g)) for g in ps] for f in ps]
        counts = Counter()
        surviving_graphs = []
        for subset in range(1 << len(interior)):
            counts['subsets'] += 1
            chosen = list(range(5)) + [5 + i for i in range(len(interior)) if subset >> i & 1]
            adjacency = [[j for j, v in enumerate(chosen) if pd[u][v] == 1] for u in chosen]
            if any(len(row) < 2 for row in adjacency):
                counts['minimum_degree_rejections'] += 1
                continue
            d = distances(adjacency)
            if d is None:
                counts['disconnected_rejections'] += 1
                continue
            if any(d[i][j] != pd[u][v] for i, u in enumerate(chosen) for j, v in enumerate(chosen)):
                counts['metric_rejections'] += 1
                continue
            n = len(chosen)
            beta = [max(sum(d[u][t] - d[v][t] for v in adjacency[u]) for t in range(n))
                    for u in range(n)]
            if any(value > 0 for value in beta[5:]):
                counts['interior_boundary_rejections'] += 1
                continue
            cuts = cut_vertices(adjacency)
            counts['cut_vertex_survivors' if cuts else 'two_connected_survivors'] += 1
            surviving_graphs.append({'beta': beta, 'cuts': cuts})
        assert counts['two_connected_survivors'] == 0
        rows.append({'cone': hit['cone'], 'metric': values, 'diameter': diameter,
                     'number_of_interior_profiles': len(interior), 'counts': dict(counts),
                     'survivors': surviving_graphs})
    report = {
        'input_survivors': len(hits), 'distinct_metric_orbits': len(metric_orbits),
        'all_nonpendant_coefficients_at_most': '3/2',
        'capping_inference': 'No survivor contains coefficient 5/2 or 3. Therefore any original metric capping to a survivor was unchanged by capping.',
        'two_connected_survivors': 0,
        'total_full_profile_subsets': sum(row['counts']['subsets'] for row in rows),
        'rows': rows,
    }
    output.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: v for k, v in report.items() if k != 'rows'}, indent=2))
    print(f'Saved {output}')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--source', type=Path, default=Path(__file__).resolve().parents[1] / 'experiments/second_turn/capped_cone_local_audit.json')
    parser.add_argument('--output', type=Path, default=Path(__file__).with_name('capped_survivors_independent_verification.json'))
    args = parser.parse_args()
    main(args.source, args.output)
