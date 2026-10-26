#!/usr/bin/env python3
"""Independent exact audit of the order-three average-deletion certificate.

Build directly in gap variables; obtain the norm from per(A A^T), not from
the coefficient array of the product polynomial. Exponents use base eight,
while the primary certificate uses base seven and triangular substitution.
Check all 720 chambers, without invoking symmetry reduction in the code.
Also check integer point evaluations against direct scalar permanents.
"""
from collections import defaultdict, Counter
from itertools import permutations
from math import prod
from random import Random
import json

PERMS = list(permutations(range(3)))
UNITS = [1 << (3*j) for j in range(6)]


def add(dst, p, factor=1):
    for k, v in p.items():
        dst[k] += factor*v


def mul(p, q):
    out = defaultdict(int)
    for a, x in p.items():
        for b, y in q.items():
            out[a+b] += x*y
    return dict(out)


def per3poly(A):
    result = defaultdict(int)
    for s in PERMS:
        add(result, mul(mul(A[0][s[0]], A[1][s[1]]), A[2][s[2]]))
    return dict(result)


def per3(A):
    return sum(prod(A[i][s[i]] for i in range(3)) for s in PERMS)


def scalar_gap(A):
    gram = [[sum(A[i][k]*A[j][k] for k in range(3)) for j in range(3)]
            for i in range(3)]
    b = per3(A)
    H = []
    for j in range(3):
        k, l = [v for v in range(3) if v != j]
        a = sum(A[i][j]*prod(A[r][k] for r in range(3) if r != i)
                for i in range(3))
        c = sum(A[i][j]*prod(A[r][l] for r in range(3) if r != i)
                for i in range(3))
        H.append(b*b+4*a*c)
    return 3*sum(H)-4*per3(gram)


def evaluate(p, x):
    return sum(v*prod(x[j]**((k >> (3*j)) & 7) for j in range(6))
               for k, v in p.items())


def build(order):
    A = [[defaultdict(int) for _ in range(3)] for _ in range(3)]
    for rank, vertex in enumerate(order):
        for i, j in enumerate(PERMS[vertex]):
            for k in range(rank+1):
                A[i][j][UNITS[k]] += 1
    gram = [[defaultdict(int) for _ in range(3)] for _ in range(3)]
    for i in range(3):
        for j in range(3):
            for k in range(3):
                add(gram[i][j], mul(A[i][k], A[j][k]))
    b = per3poly(A)
    G = defaultdict(int)
    add(G, mul(b, b), 9)
    for j in range(3):
        others = [k for k in range(3) if k != j]
        pair = []
        for k in others:
            coeff = defaultdict(int)
            for i in range(3):
                r, s = [v for v in range(3) if v != i]
                add(coeff, mul(A[i][j], mul(A[r][k], A[s][k])))
            pair.append(coeff)
        add(G, mul(*pair), 12)
    add(G, per3poly(gram), -4)
    return A, {k: v for k, v in G.items() if v}


def main():
    primary = {tuple(r['order']): r
               for r in json.load(open('round3_deletion_n3_birkhoff.json'))}
    rng = Random(260306)
    counts = Counter()
    point_checks = 0
    primary_matches = 0
    equality_patterns = Counter()
    global_min = None
    for order in permutations(range(6)):
        A, G = build(order)
        assert G and min(G.values()) > 0, order
        global_min = min(global_min or min(G.values()), min(G.values()))
        counts[len(G)] += 1
        if order in primary:
            row = primary[order]
            assert len(G) == row['terms'] and min(G.values()) == row['min']
            primary_matches += 1
        pure = [G.get(6*u, 0) for u in UNITS]
        assert pure[0] == 0
        assert all(pure[j] > 0 for j in (1, 2, 4, 5))
        assert pure[3] >= 0
        equality_patterns['pure_gap3_zero' if pure[3] == 0 else 'pure_gap3_positive'] += 1
        if pure[3] == 0:
            tail = [[sum(int(PERMS[v][i] == j) for v in order[3:])
                     for j in range(3)] for i in range(3)]
            assert tail == [[1]*3 for _ in range(3)]
        points = [[1]*6, [rng.randrange(5) for _ in range(6)]]
        points += [[int(i == j) for j in range(6)] for i in range(6)]
        for x in points:
            Anum = [[evaluate(A[i][j], x) for j in range(3)] for i in range(3)]
            assert evaluate(G, x) == scalar_gap(Anum), (order, x)
            point_checks += 1
    report = {
        'status': 'all exact integer checks passed',
        'method': 'direct-gap construction; per(AA^T) norm; base8 polynomial keys',
        'chambers_checked_without_symmetry_reduction': sum(counts.values()),
        'primary_chamber_counts_and_minima_matched': primary_matches,
        'positive_coefficient_positions': sum(k*v for k, v in counts.items()),
        'minimum_positive_coefficient': global_min,
        'positive_term_count_histogram': dict(sorted(counts.items())),
        'independent_scalar_integer_point_checks': point_checks,
        'pure_gap_equality_patterns': dict(equality_patterns),
        'equality_conclusion': 'For A with common row/column sum, defect=0 iff A is a scalar multiple of the all-ones matrix.'
    }
    with open('round3_deletion_n3_independent_audit.json', 'w') as f:
        json.dump(report, f, indent=2)
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
