#!/usr/bin/env python3
"""Independent exact audits of the all-radius rooted metric representative.

The theorem is proved in the companion Lean file.  These tests reconstruct
profiles directly from full metric distances, without using the clipped
signature formula, to audit the implementation and the theorem's application.
"""

from collections import Counter
from itertools import combinations, product
from pathlib import Path
import json
import random
import time


def is_metric(m):
    n = len(m)
    return (all(m[i][i] == 0 for i in range(n))
            and all(m[i][j] == m[j][i] > 0 for i, j in combinations(range(n), 2))
            and all(m[i][k] <= m[i][j] + m[j][k]
                    for i in range(n) for j in range(n) for k in range(n)))


def canonical(m, root, radius):
    n = len(m)
    threshold = 2 * radius + 1
    original_d = m[root]
    d = [x if x <= radius else threshold for x in original_d]
    result = [[0] * n for _ in range(n)]
    for i, j in combinations(range(n), 2):
        h = original_d[i] + original_d[j] - m[i][j]
        result[i][j] = result[j][i] = d[i] + d[j] - min(h, threshold)
    return result


def signature(m, root, radius):
    others = [i for i in range(len(m)) if i != root]
    return (tuple(min(m[root][i], radius + 1) for i in others),
            tuple(min(m[root][i] + m[root][j] - m[i][j], 2 * radius + 1)
                  for i, j in combinations(others, 2)))


def profiles_from_full_metric(m, root, radius):
    n = len(m)
    others = [i for i in range(n) if i != root]
    positive = set()
    for r in range(1, radius + 1):
        for eps in product(range(-r, r + 1), repeat=n - 1):
            f = [0] * n
            f[root] = r
            for i, e in zip(others, eps):
                f[i] = m[root][i] + e
            if min(f) <= 0:
                continue
            if any(f[i] + f[j] < m[i][j] for i, j in combinations(range(n), 2)):
                continue
            if any(not any(f[i] + f[j] == m[i][j] for j in range(n)) for i in range(n)):
                continue
            positive.add((r, *eps))
    marked = {i: (m[i][root], *(m[i][j] - m[root][j] for j in others))
              for i in range(n) if m[root][i] <= radius}
    return positive, marked


def check_one(m, root, radius, stats, profiles=False):
    c = canonical(m, root, radius)
    assert is_metric(c)
    assert signature(m, root, radius) == signature(c, root, radius)
    assert max(c[root]) <= 2 * radius + 1
    assert max(map(max, c)) <= 4 * radius + 2
    assert canonical(c, root, radius) == c
    stats['rooted_metric_instances'] += 1
    if profiles:
        a = profiles_from_full_metric(m, root, radius)
        b = profiles_from_full_metric(c, root, radius)
        assert a == b
        stats['full_profile_comparisons'] += 1
        stats['positive_profiles_compared'] += len(a[0])
        stats['marked_profiles_compared'] += len(a[1])


def weighted_metric(n, rng):
    choices = [1, 2, 3, 4, 5, 6, 11, 37, 10000, 1000003]
    m = [[0] * n for _ in range(n)]
    for i, j in combinations(range(n), 2):
        m[i][j] = m[j][i] = rng.choice(choices)
    for k in range(n):
        for i in range(n):
            for j in range(n):
                m[i][j] = min(m[i][j], m[i][k] + m[k][j])
    return m


def main():
    started = time.monotonic()
    stats = Counter()
    pairs = list(combinations(range(4), 2))
    for values in product(range(1, 6), repeat=6):
        m = [[0] * 4 for _ in range(4)]
        for (i, j), x in zip(pairs, values):
            m[i][j] = m[j][i] = x
        if not is_metric(m):
            continue
        stats['exhaustive_four_point_metrics'] += 1
        for root in range(4):
            for radius in (0, 1, 2, 3):
                check_one(m, root, radius, stats)
    rng = random.Random(20261102)
    for n in (3, 4, 5, 6):
        for _ in range(24):
            m = weighted_metric(n, rng)
            assert is_metric(m)
            stats['adversarial_weighted_metrics'] += 1
            for root in range(n):
                for radius in (1, 2):
                    check_one(m, root, radius, stats, profiles=True)
    for radius in range(21):
        r = radius
        m = [[0, r + 1, 2 * r + 1, r + 1],
             [r + 1, 0, r + 1, 2 * r + 2],
             [2 * r + 1, r + 1, 0, r + 1],
             [r + 1, 2 * r + 2, r + 1, 0]]
        assert is_metric(m)
        h12 = m[0][1] + m[0][2] - m[1][2]
        h23 = m[0][2] + m[0][3] - m[2][3]
        h13 = m[0][1] + m[0][3] - m[1][3]
        assert h12 == h23 == 2 * r + 1 and h13 == 0
        assert h12 + h23 - h13 == 2 * m[0][2]
        stats['sharp_four_point_instances'] += 1
        # Five-point wheel: four cyclic vertices all forced to root
        # distance T, with an opposite pair forcing diameter 2T.
        t = 2 * r + 1
        w = [[0 if i == j else t for j in range(5)] for i in range(5)]
        w[1][3] = w[3][1] = w[2][4] = w[4][2] = 2 * t
        assert is_metric(w)
        assert w[1][3] == 4 * r + 2
        assert w[0][1] + w[0][3] - w[1][3] == 0
        assert signature(w, 0, r) == signature(canonical(w, 0, r), 0, r)
        stats['sharp_five_point_instances'] += 1
    report = {'all_passed': True, 'counts': dict(stats), 'seed': 20261102,
              'seconds': round(time.monotonic() - started, 3),
              'scope': 'Independent finite adversarial audit. The universal theorem and sharpness are proved in Lean, not inferred from these tests.'}
    (Path(__file__).resolve().parent / 'rooted_metric_exact_audit.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
