#!/usr/bin/env python3
"""Exact rational linear-algebra certificate for the three five-point cones.

No floating-point operations or external packages are used. The external
coverage theorem says that every five-point metric is, up to relabelling,
a nonnegative combination of the ten columns in one of these matrices.
This script verifies the half-integral inverse matrices, the pendant
coefficient interpretation, and the generator facts needed for capping.
"""

from argparse import ArgumentParser
from fractions import Fraction
from itertools import combinations
import json
from pathlib import Path


PAIRS = tuple(combinations(range(5), 2))
NONPENDANT = (
    ((0, 1), (1, 2), (2, 3), (3, 4), (4, 0)),
    ((0, 2), (0, 3), (1, 2), (1, 3), None),
    ((0, 2), (0, 3), (1, 4), (1, 3), None),
)


def generator(subset):
    if subset is None:
        return [2 if (i < 2) == (j < 2) else 1 for i, j in PAIRS]
    return [int((i in subset) != (j in subset)) for i, j in PAIRS]


def inverse(matrix):
    n = len(matrix)
    a = [[Fraction(v) for v in row] + [Fraction(i == j) for j in range(n)]
         for i, row in enumerate(matrix)]
    for j in range(n):
        pivot = next(i for i in range(j, n) if a[i][j])
        a[j], a[pivot] = a[pivot], a[j]
        scale = a[j][j]
        a[j] = [v / scale for v in a[j]]
        for i in range(n):
            if i != j:
                scale = a[i][j]
                a[i] = [v - scale * w for v, w in zip(a[i], a[j])]
    assert all(a[i][j] == (i == j) for i in range(n) for j in range(n))
    return [row[n:] for row in a]


def matrix_of(column):
    m = [[0] * 5 for _ in range(5)]
    for (i, j), value in zip(PAIRS, column):
        m[i][j] = m[j][i] = value
    return m


def main(output):
    rows = []
    for kind, nonpendant in enumerate(NONPENDANT, 1):
        columns = [generator((i,)) for i in range(5)] + [generator(s) for s in nonpendant]
        matrix = [[column[i] for column in columns] for i in range(10)]
        inv = inverse(matrix)
        assert all((2 * value).denominator == 1 for row in inv for value in row)
        twice_inverse = [[int(2 * value) for value in row] for row in inv]
        # Verify both exact integer matrix identities, not only elimination.
        for i in range(10):
            for j in range(10):
                assert sum(matrix[i][k] * twice_inverse[k][j] for k in range(10)) == 2 * (i == j)
                assert sum(twice_inverse[i][k] * matrix[k][j] for k in range(10)) == 2 * (i == j)
        generators = [matrix_of(column) for column in columns]
        root_witnesses = []
        for b in range(5):
            candidates = []
            for c, e in combinations([v for v in range(5) if v != b], 2):
                products = [Fraction(m[b][c] + m[b][e] - m[c][e], 2) for m in generators]
                assert all(value in (0, 1) for value in products)
                assert products[:5] == [int(i == b) for i in range(5)]
                if all(value == 0 for value in products[5:]):
                    candidates.append((c, e))
            assert candidates
            root_witnesses.append({'root': b, 'zero_nonpendant_product_pairs': candidates})
        assert all(value in (0, 1, 2) for column in columns for value in column)
        rows.append({
            'cone': kind,
            'nonpendant_splits': nonpendant,
            'last_generator_if_null': 'K_2,3 metric with parts {0,1} and {2,3,4}',
            'generator_matrix_rows_in_pair_order': matrix,
            'twice_inverse_matrix': twice_inverse,
            'pendant_minimum_gromov_product_witnesses': root_witnesses,
            'identities_verified': 'A*(2A^-1)=(2A^-1)*A=2I over integers',
        })
    report = {
        'pair_order': PAIRS,
        'column_order': 'singleton splits 0,1,2,3,4 followed by the listed five nonpendant generators',
        'conclusion': 'Every integral metric in one of the three cones has unique half-integral cone coefficients. In each cone the singleton coefficient at b equals the minimum Gromov product rooted at b. Every nonpendant generator has triple Gromov products 0 or 1.',
        'external_input_not_proved_by_this_script': 'The three cones and their relabellings cover the five-point metric cone.',
        'cones': rows,
    }
    output.write_text(json.dumps(report, indent=2) + '\n')
    print(f'PASS: all three exact inverse certificates, pendant witnesses and capping generator facts. Saved {output}')


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=Path(__file__).with_name('five_point_cone_exact_matrices.json'))
    main(parser.parse_args().output)
