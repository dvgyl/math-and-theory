#!/usr/bin/env python3
"""Check the order-five certificate with exact integer arithmetic.

The program uses the permutation definition of the permanent. It does not read
Lean source files or generated coefficient tables. The packed monomial and
binomial-transform methods follow the source research checkers.

Run: python3 check_coefficients.py --output coefficient-results.json
This computation supplements the Lean proof. It is not a Lean kernel check.
"""
import argparse
from collections import defaultdict
from hashlib import sha256
from itertools import permutations
import json
from math import comb, prod
from pathlib import Path

N = 5
BASE = 16
UNITS = [BASE**j for j in range(N)]
ORDERS = list(permutations(range(N)))


def multiply(left, right):
    """Multiply polynomials. Exponents cannot carry because each degree is at most 10."""
    result = defaultdict(int)
    for a, x in left.items():
        for b, y in right.items():
            result[a + b] += x * y
    return {a: x for a, x in result.items() if x}


def permanent(matrix):
    result = defaultdict(int)
    for order in ORDERS:
        term = {0: 1}
        for i, j in enumerate(order):
            term = multiply(term, matrix[i][j])
        for a, x in term.items():
            result[a] += x
    return dict(result)


def matrix_product_transpose(matrix):
    result = []
    for i in range(N):
        row = []
        for j in range(N):
            entry = defaultdict(int)
            for k in range(N):
                for a, x in multiply(matrix[i][k], matrix[j][k]).items():
                    entry[a] += x
            row.append(dict(entry))
        result.append(row)
    return result


def reindex(poly, order):
    ranks = {original: rank for rank, original in enumerate(order)}
    return {sum((a // UNITS[j] % BASE) * UNITS[ranks[j]] for j in range(N)): x
            for a, x in poly.items()}


def shear(poly, j, sign):
    result = defaultdict(int)
    for a, x in poly.items():
        exponent = a // UNITS[j] % BASE
        for h in range(exponent + 1):
            result[a - h * UNITS[j] + h * UNITS[j-1]] += x * comb(exponent, h) * sign**h
    return {a: x for a, x in result.items() if x}


def gaps(poly, order):
    result = reindex(poly, order)
    for j in range(N-1, 0, -1):
        result = shear(result, j, 1)
    return result


def inverse_gaps(poly):
    for j in range(1, N):
        poly = shear(poly, j, -1)
    return poly


def evaluate(poly, weights):
    return sum(x * prod(weights[j]**(a // UNITS[j] % BASE) for j in range(N))
               for a, x in poly.items())


def check():
    matrix = [[{UNITS[(j-i) % N]: 1} for j in range(N)] for i in range(N)]
    p = permanent(matrix)
    q = permanent(matrix_product_transpose(matrix))
    square = multiply(p, p)
    defect = {a: 625 * square.get(a, 0) - 24 * q.get(a, 0) for a in set(square) | set(q)}
    defect = {a: x for a, x in defect.items() if x}
    assert len(p) == 26 and sum(p.values()) == 120
    assert all(sum(a // u % BASE for u in UNITS) == 10 for a in defect)
    canonical = [(0, 1) + tail for tail in permutations((2, 3, 4))]
    cover = [(tuple((a*x+b) % N for x in order), order, a, b)
             for order in canonical for a in range(1, N) for b in range(N)]
    assert len(cover) == 120 and {x[0] for x in cover} == set(ORDERS)
    assert len({x[0] for x in cover}) == len(cover)
    zero_positions = {10*UNITS[0]} | {9*UNITS[0]+UNITS[j] for j in range(1, N)}
    results = []
    for order in ORDERS:
        poly = gaps(defect, order)
        assert inverse_gaps(poly) == reindex(defect, order)
        assert len(poly) == 996 and min(poly.values()) == 484
        assert not (set(poly) & zero_positions)
        pure = [poly[10*UNITS[j]] for j in range(1, N)]
        assert pure == [233296, 44209, 484, 601]
        residual = dict(poly)
        for j in range(1, N):
            residual[10*UNITS[j]] -= 484
        assert min(residual.values()) >= 0
        encoded = json.dumps(sorted(poly.items()), separators=(',', ':')).encode()
        results.append({'order': order, 'positive': 996, 'zeros': 5,
                        'minimum': 484, 'pure_gap_coefficients': pure,
                        'sha256': sha256(encoded).hexdigest()})
    witness = [1, 1, 0, 0, 0]
    assert evaluate(p, witness) == 2
    assert evaluate(q, witness) == 84
    assert evaluate(defect, witness) == 484
    assert evaluate(defect, [1]*5) == 0
    return {'status': 'PASS', 'arithmetic': 'exact integers', 'order': 5,
            'orderings': 120, 'canonical_orderings': 6, 'positions_per_ordering': 1001,
            'total_coefficient_positions': 120120, 'positive_positions': 119520,
            'zero_positions': 600, 'sharp_constant': 484, 'chambers': results}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=Path('coefficient-results.json'))
    args = parser.parse_args()
    result = check()
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k != 'chambers'}, indent=2))
