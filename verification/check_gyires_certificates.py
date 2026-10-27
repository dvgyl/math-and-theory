#!/usr/bin/env python3
"""Check that the Gyires reports cover the finite ranges used in the paper.

This checks report structure and coverage. Recompute the reports with the
certificate programs to check their arithmetic.
"""
import argparse
import json
from itertools import permutations
from math import comb, gcd
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--support', type=Path,
                    default=ROOT / 'research-notes/gyires-complete-support/results')
parser.add_argument('--extensions', type=Path,
                    default=ROOT / 'research-notes/gyires-extensions/results')
args = parser.parse_args()
errors = []


def require(condition, message):
    if not condition:
        errors.append(message)


def read_report(directory, name):
    return json.loads((directory / name).read_text(encoding='utf-8'))


for n in (6, 7):
    report = read_report(args.support, f'circ_gap_n{n}_all_results.json')
    rows = report['chambers']
    require(report.get('status') == 'passed', f'Circulant order {n}: report is not complete')
    units = [a for a in range(1, n) if gcd(a, n) == 1]
    expected = {p for p in permutations(range(n)) if p[0] == 0
                and not any(tuple(a * x % n for x in p) < p for a in units)}
    keys = [tuple(row['permutation']) for row in rows]
    require(report['n'] == n, f'Circulant order {n}: incorrect order')
    require(len(keys) == len(set(keys)) and set(keys) == expected,
            f'Circulant order {n}: incomplete or duplicate chambers')
    for row in rows:
        require(row['negative_terms'] == 0 and row['min_coefficient'] > 0,
                f'Circulant order {n}: failed coefficient check')
        require(row['nonzero_terms'] == comb(3 * n - 1, n - 1) - n,
                f'Circulant order {n}: incorrect coefficient coverage')

def check_permutation_report(filename, maximum):
    report = read_report(args.extensions, filename)
    rows = report['results']
    require(report.get('status') == 'passed', 'Permutation polynomial: report is not complete')
    keys = [(row['n'], row['chamber']) for row in rows]
    expected = {(n, chamber) for n in range(3, maximum + 1) for chamber in range(3)}
    require(report['max_n'] == maximum, 'Permutation polynomial: incorrect maximum order')
    require(len(keys) == len(set(keys)) and set(keys) == expected,
            'Permutation polynomial: incomplete or duplicate chambers')
    for row in rows:
        require(row['negative'] == 0 and row['positive'] > 0,
                'Permutation polynomial: failed coefficient check')
        require(row['positive'] + row['zero'] + row['negative'] == comb(2 * row['n'] + 2, 2),
                'Permutation polynomial: incorrect coefficient coverage')
        require(row['n'] == 3 or row['zero'] == 0,
                'Permutation polynomial: expected strict coefficient positivity')


check_permutation_report('independent_finite.json', 47)
check_permutation_report('permutation-alternative-finite.json', 93)

report = read_report(args.support, 'rank2_bernstein_certificate.json')
rows = report['records']
require(report['status'] == 'passed' and report['exhaustive_profile_pairs'] is True,
        'Rank two: report is not an exhaustive completed check')
require((report['first_order'], report['last_completed_order'], report['requested_last_order'])
        == (2, 15, 15), 'Rank two: incorrect requested or completed range')
keys = [row['n'] for row in rows]
require(len(keys) == len(set(keys)) and set(keys) == set(range(2, 16)),
        'Rank two: incomplete or duplicate orders')
for row in rows:
    n = row['n']
    intervals = (n * (n + 1) // 2 - 1) ** 2 - 2 * comb(n + 2, 4)
    require(row['tested'] == intervals, f'Rank two order {n}: incomplete interval coverage')
    require(row['fail_strong_contraction'] == [0, 0], f'Rank two order {n}: failed coefficients')
    require(row['coefficient_counts_strong_contraction'] == [intervals * (4 * n + 1)] * 2,
            f'Rank two order {n}: incorrect coefficient coverage')

rows = read_report(args.support, 'deletion_n3_birkhoff.json')
keys = [tuple(row['order']) for row in rows]
expected = {(0,) + p for p in permutations(range(1, 6))}
require(len(keys) == len(set(keys)) and set(keys) == expected,
        'Cubic deletion: incomplete or duplicate primary chambers')
require(all(row['negative'] == 0 and row['zero_pure_rays_are_uniform'] is True for row in rows),
        'Cubic deletion: failed coefficients or equality check')
report = read_report(args.support, 'deletion_n3_independent_audit.json')
require(report['chambers_checked_without_symmetry_reduction'] == 720
        and report['primary_chamber_counts_and_minima_matched'] == 120
        and report['independent_scalar_integer_point_checks'] == 5760,
        'Cubic deletion: incomplete independent coverage')

print(json.dumps({'status': 'FAIL' if errors else 'PASS', 'errors': errors}, indent=2))
raise SystemExit(bool(errors))
