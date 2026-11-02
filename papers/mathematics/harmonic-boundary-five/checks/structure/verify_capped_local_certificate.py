#!/usr/bin/env python3
"""Check the finite capped-cone certificate without a SAT solver or search.

1. Reconstruct every radius-two profile set from its ten-entry local signature.
2. Check a direct selected-vertex witness for SAT, or replay every justified
   propagation step and both branches of an explicit contradiction tree for UNSAT.
3. Independently enumerate all 3 * 7**5 * 2**5 capped coefficient choices,
   using the certified truth table only, and verify the complete survivor set.

This verifies the finite certificate. The graph-to-local-model implication,
three-cone coverage and capping lemma are mathematical inputs proved in the note.
"""
from itertools import combinations, permutations, product
from pathlib import Path
from collections import Counter
import argparse
import json
import time

PAIRS4 = tuple(combinations(range(4), 2))
PAIRS5 = tuple(combinations(range(5), 2))
PERMS4 = tuple(permutations(range(4)))


def bits(mask):
    while mask:
        low = mask & -mask
        yield low.bit_length() - 1
        mask ^= low


def profiles_from_signature(key):
    ds = key[:4]
    h = [[0] * 4 for _ in range(4)]
    for (i, j), value in zip(PAIRS4, key[4:]):
        h[i][j] = h[j][i] = value
    mandatory = [(0, 0, 0, 0, 0)]
    for i, d in enumerate(ds):
        if d <= 2:
            eps = [d - h[i][j] for j in range(4)]
            eps[i] = -d
            mandatory.append((d, *eps))
    interior = []
    for r in (1, 2):
        for eps in product(range(-r, r + 1), repeat=4):
            if -r not in eps:
                continue
            if any(ds[i] + eps[i] <= 0 for i in range(4)):
                continue
            if any(eps[i] + eps[j] < -h[i][j] for i, j in PAIRS4):
                continue
            if any(eps[i] != -r and not any(
                j != i and eps[i] + eps[j] == -h[i][j]
                for j in range(4)) for i in range(4)):
                continue
            interior.append((r, *eps))
    return mandatory, interior


def check_type(row, stats):
    key = tuple(row['type'])
    assert len(key) == 10
    assert all(1 <= x <= 3 for x in key[:4])
    assert all(0 <= x <= 5 for x in key[4:])
    expected_b, expected_i = profiles_from_signature(key)
    ps = [tuple(p) for p in row['profiles']]
    nb, n = row['mandatory_count'], len(ps)
    assert nb == len(expected_b)
    assert ps[:nb] == expected_b
    assert set(ps[nb:]) == set(expected_i)
    assert len(ps) == len(set(ps)) == len(expected_b) + len(expected_i)
    assert row['profile_count'] == n
    all_mask = (1 << n) - 1
    mandatory = (1 << nb) - 1
    adj = [sum(1 << v for v in range(n)
               if max(abs(ps[u][k] - ps[v][k]) for k in range(5)) == 1)
           for u in range(n)]
    near = {u for u in range(n) if ps[u][0] <= 1}
    one = {u for u in range(n) if ps[u][0] == 1}
    two_mask = sum(1 << u for u in range(n) if ps[u][0] == 2)
    need_match = 3 in key[:4]
    close = [[sum(1 << v for v in bits(adj[u]) if ps[u][k] > ps[v][k])
              for k in range(5)] for u in range(n)]
    far = [[sum(1 << v for v in bits(adj[u]) if ps[u][k] < ps[v][k])
            for k in range(5)] for u in range(n)]
    assert all(abs(ps[u][k] - ps[v][k]) <= 1
               for u in range(n) for v in bits(adj[u]) for k in range(5))

    def matching(selected):
        # Independently check two disjoint edges by explicit edge pairs.
        pairs = [(u, v) for u in one if selected >> u & 1
                 for v in bits(adj[u] & selected & two_mask)]
        return any(u != w and v != t for q, (u, v) in enumerate(pairs)
                   for w, t in pairs[q + 1:])

    def valid(selected):
        if selected & ~all_mask or mandatory & ~selected:
            return False
        for u in near:
            if not selected >> u & 1:
                continue
            if (adj[u] & selected).bit_count() < (2 if u < nb else 4):
                return False
            if u >= nb:
                for k in range(5):
                    score = sum(ps[u][k] - ps[v][k]
                                for v in bits(adj[u] & selected))
                    if score > 0:
                        return False
        return not need_match or matching(selected)

    def lower(u, k, available, forced):
        return (close[u][k] & forced).bit_count() - (far[u][k] & available).bit_count()

    def check_tree(node, available, forced):
        stats['unsat_tree_nodes'] += 1
        assert not forced & ~available
        for step in node['steps']:
            stats['propagation_steps'] += 1
            rule = step[0]
            if rule == 'two_force':
                assert len(step) == 1 and need_match and matching(available)
                choices = two_mask & available
                assert choices.bit_count() == 2
                forced |= choices
            else:
                u = step[1]
                assert 0 <= u < n and u in near and available >> u & 1
                ub = 1 << u
                threshold = 2 if u < nb else 4
                degree = (adj[u] & available).bit_count()
                if rule == 'degree_remove':
                    assert len(step) == 2 and not forced & ub and degree < threshold
                    available &= ~ub
                elif rule == 'degree_force':
                    assert len(step) == 2 and forced & ub and degree == threshold
                    forced |= adj[u] & available
                elif rule in ('score_remove', 'score_force'):
                    assert len(step) == 3 and u >= nb
                    k = step[2]
                    assert 0 <= k < 5
                    value = lower(u, k, available, forced)
                    if rule == 'score_remove':
                        assert not forced & ub and value > 0
                        available &= ~ub
                    else:
                        assert forced & ub and value == 0
                        forced |= far[u][k] & available
                        available &= ~(close[u][k] & ~forced)
                else:
                    raise AssertionError(('unknown rule', step))
            assert not forced & ~available
        if 'contradiction' in node:
            assert 'branch' not in node
            why = node['contradiction']
            kind = why['kind']
            stats['contradiction_' + kind] += 1
            if kind == 'forced_excluded':
                assert forced & ~available
            elif kind == 'matching':
                assert need_match and not matching(available)
            elif kind == 'degree':
                u = why['u']
                assert u in near and forced >> u & 1
                assert (adj[u] & available).bit_count() < (2 if u < nb else 4)
            elif kind == 'score':
                u, k = why['u'], why['k']
                assert u in near and u >= nb and forced >> u & 1 and 0 <= k < 5
                assert lower(u, k, available, forced) > 0
            elif kind == 'invalid_complete':
                assert available == forced and not valid(forced)
            else:
                raise AssertionError(('unknown contradiction', why))
            return
        branch = node['branch']
        u = branch['vertex']
        assert 0 <= u < n and available >> u & 1 and not forced >> u & 1
        stats['branch_nodes'] += 1
        check_tree(branch['include'], available, forced | (1 << u))
        check_tree(branch['exclude'], available & ~(1 << u), forced)

    cert = row['certificate']
    if cert['kind'] == 'sat':
        assert row['feasible'] is True
        assert valid(cert['selected'])
        stats['sat_witnesses'] += 1
        result = True
    else:
        assert cert['kind'] == 'unsat' and row['feasible'] is False
        check_tree(cert['tree'], all_mask, mandatory)
        stats['unsat_certificates'] += 1
        result = False
    stats['maximum_local_profiles'] = max(stats['maximum_local_profiles'], n)
    return key, result


def signature(m, root):
    other = [u for u in range(5) if u != root]
    d = [m[root][u] for u in other]
    h = [[d[i] + d[j] - m[other[i]][other[j]] for j in range(4)] for i in range(4)]
    return min(tuple(min(d[i], 3) for i in p) +
               tuple(min(h[p[i]][p[j]], 5) for i, j in PAIRS4) for p in PERMS4)


def cone_check(truth):
    cones = [((0, 1), (1, 2), (2, 3), (3, 4), (4, 0)),
             ((0, 2), (0, 3), (1, 2), (1, 3), None),
             ((0, 2), (0, 3), (1, 4), (1, 3), None)]
    counts = Counter()
    by_cone = []
    survivors = []
    key_cache = {}
    for number, cone in enumerate(cones, 1):
        generators = []
        for part in cone:
            if part is None:
                generators.append([2 if (i < 2) == (j < 2) else 1 for i, j in PAIRS5])
            else:
                generators.append([int((i in part) != (j in part)) for i, j in PAIRS5])
        cc = Counter()
        for weights in product(range(7), repeat=5):
            raw = [sum(weights[g] * generators[g][e] for g in range(5)) for e in range(10)]
            for pendant in product((0, 1), repeat=5):
                cc['nominal_coefficient_choices'] += 1
                twice = [x + pendant[i] + pendant[j] for x, (i, j) in zip(raw, PAIRS5)]
                if any(x % 2 for x in twice):
                    continue
                cc['integral_representatives'] += 1
                values = tuple(x // 2 for x in twice)
                if not all(values):
                    cc['coincident_points'] += 1
                    continue
                if max(values) <= 2:
                    cc['diameter_at_most_two'] += 1
                    continue
                cc['positive_diameter_at_least_three'] += 1
                if values in key_cache:
                    good = key_cache[values]
                else:
                    m = [[0] * 5 for _ in range(5)]
                    for (i, j), x in zip(PAIRS5, values):
                        m[i][j] = m[j][i] = x
                    good = True
                    for root in range(5):
                        key = signature(m, root)
                        assert key in truth, ('missing local certificate', key)
                        if not truth[key]:
                            good = False
                            break
                    key_cache[values] = good
                if not good:
                    cc['local_infeasibility_rejections'] += 1
                    continue
                cc['locally_feasible_representatives'] += 1
                assert max(weights) <= 3, ('uncapping obstruction', number, weights)
                assert max(values) in (3, 4)
                if max(values) == 4:
                    special = [[0] * 5 for _ in range(5)]
                    for (i, j), value in zip(PAIRS5, values):
                        special[i][j] = special[j][i] = value
                    far_pairs = [(i, j) for i, j in PAIRS5 if special[i][j] == 4]
                    assert len(far_pairs) == 1
                    aa = set(far_pairs[0])
                    cc_vertices = set(range(5)) - aa
                    assert all(special[i][j] == 2 for i in aa for j in cc_vertices)
                    assert all(special[i][j] == 3 for i, j in combinations(cc_vertices, 2))
                survivors.append((number, weights, pendant, values))
        assert cc['nominal_coefficient_choices'] == 32 * 7**5
        by_cone.append({'cone': number, **dict(cc)})
        counts.update(cc)
    assert counts['nominal_coefficient_choices'] == 3 * 32 * 7**5
    return dict(counts), by_cone, survivors


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--certificate', type=Path, default=Path(__file__).with_name('capped_local_proof_certificate.json'))
    ap.add_argument('--output', type=Path, default=Path(__file__).with_name('capped_local_certificate_verification.json'))
    ap.add_argument('--skip-cones', action='store_true', help='check every local proof but omit the coefficient enumeration')
    args = ap.parse_args()
    start = time.monotonic()
    data = json.loads(args.certificate.read_text())
    stats = Counter()
    truth = {}
    for row in data['type_results']:
        key, value = check_type(row, stats)
        assert key not in truth
        truth[key] = value
    report = {'certificate_scope': 'Exact local SAT witnesses and explicit UNSAT proof trees, independently replayed; complete capped-cone enumeration unless skipped.',
              'certified_local_types': len(truth), 'local_proof_statistics': dict(stats)}
    if not args.skip_cones:
        counts, by_cone, survivors = cone_check(truth)
        proposed = {(h['cone'], tuple(h['twice_nonpendant_weights']), tuple(h['twice_pendant_weights']), tuple(h['metric'])) for h in data['hits']}
        assert set(survivors) == proposed and len(survivors) == 15
        assert counts == data['counts']
        report.update({'capped_cone_counts': counts, 'by_cone': by_cone,
                       'survivor_records_exactly_verified': len(survivors),
                       'maximum_surviving_twice_nonpendant_weight': max(max(h[1]) for h in survivors),
                       'surviving_metric_diameters': sorted({max(h[3]) for h in survivors}),
                       'diameter_four_special_metric_representatives_verified': sum(max(h[3]) == 4 for h in survivors)})
    report['seconds'] = round(time.monotonic() - start, 3)
    report['status'] = 'verified'
    args.output.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
