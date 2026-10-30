#!/usr/bin/env python3
"""Independent exact check of the width-109 nonnegative factorization of C_6 tensor C_6.

The matrix C_6 is rebuilt from its definition, not read from the certificate, and compared
with the stored copy. The script then checks that both stored factors are entrywise
nonnegative and that their product equals the Kronecker square entry by entry, and computes
the ordinary ranks of A and C_6 by Gaussian elimination over the rationals. It uses only
the standard library and exact fractions.
"""
import json
import sys
from fractions import Fraction
from pathlib import Path

SEED = [[17, 17, 1, 1], [1, 17, 17, 1], [1, 1, 17, 17], [17, 1, 1, 17]]


def witness(t):
    s, eps = t + 1, Fraction(1, 100800 * t * (3 * t + 1))
    n = 4 + s
    c = [[Fraction(0)] * n for _ in range(n)]
    for i in range(4):
        for j in range(4):
            c[i][j] = Fraction(SEED[i][j])
    for i in range(s):
        for j in range(s):
            c[4 + i][4 + j] = 1 + (eps if i == j else 0)
    return c


def rank(rows):
    m, r = [row[:] for row in rows], 0
    for col in range(len(m[0])):
        pivot = next((i for i in range(r, len(m)) if m[i][col] != 0), None)
        if pivot is None:
            continue
        m[r], m[pivot] = m[pivot], m[r]
        for i in range(len(m)):
            if i != r and m[i][col] != 0:
                f = m[i][col] / m[r][col]
                m[i] = [a - f * b for a, b in zip(m[i], m[r])]
        r += 1
    return r


def main(path):
    data = json.loads(Path(path).read_text())
    c = witness(6)
    n = len(c)
    assert [[Fraction(x) for x in row] for row in data['C']] == c, 'stored C differs from C_6'
    left = [[Fraction(x) for x in row] for row in data['L']]
    right = [[Fraction(x) for x in row] for row in data['R']]
    width = len(right)
    assert len(left) == n * n and all(len(row) == width for row in left), 'shape of L'
    assert all(len(row) == n * n for row in right), 'shape of R'
    assert all(x >= 0 for row in left + right for x in row), 'negative factor entry'
    columns = list(zip(*right))
    for i in range(n * n):
        for j in range(n * n):
            target = c[i // n][j // n] * c[i % n][j % n]
            assert sum(a * b for a, b in zip(left[i], columns[j])) == target, (i, j)
    result = {'status': 'PASS', 'order': n, 'factorization_width': width,
              'kronecker_entries_checked': (n * n) ** 2,
              'rank_A': rank([[Fraction(x) for x in row] for row in SEED]), 'rank_C': rank(c)}
    assert result['rank_A'] == 3 and result['rank_C'] == 10 and width == 109
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main(sys.argv[1] if len(sys.argv) > 1 else Path(__file__).with_name('C11_NMF109.json'))
