#!/usr/bin/env python3
"""Independent exact check of the short-chain certificates.

Standard library only.  For every short-chain size a = 1..5 and every endpoint
word (Dyck word with a letters L and a letters U) the certificate supplies a
polynomial F_{a,w} in the 2a+1 gap variables.  This script checks:

  1. the chamber list is complete and has no duplicates;
  2. every polynomial has the stated number of variables, total degree <= a
     and zero constant term;
  3. nonnegativity on the closed orthant: for a <= 3 every coefficient is a
     positive integer; for a = 4, 5 every square weight and every remainder
     coefficient is nonnegative and the squares plus the remainder expand to
     the polynomial exactly;
  4. at every integer point x >= 0 with |x| <= a, the polynomial equals
     (a+b)! [t]Omega_P(t) / (b-1)! for the poset P built from (a, w, x), with
     b = |x|; Omega_P is computed here from scratch by counting multichains
     of order ideals and extracting the linear coefficient from finite
     differences.  At x = 0 the polynomial must vanish;
  5. the degree-one coefficient of x_j in the nonnegative part equals (a-1)!
     when fewer than a short-chain elements are incomparable with the gap
     segment j, and 0 otherwise (the quantitative linear-coefficient bound);
  6. optionally (--extra N), agreement at N further random integer points with
     |x| > a, as an out-of-sample sanity check of polynomiality.

It also recomputes the three worked examples of the manuscript.

Usage (from the package root):
  python3 certificate/check_certificates.py [--extra 3] [--json OUT.json]
By default the three certificate files are read from certificate/data/.
"""
import argparse
import gzip
import json
import lzma
import math
import random
import sys
import time
from fractions import Fraction
from pathlib import Path

DATA = Path(__file__).resolve().parent / 'data'


def load(path):
    opener = open
    if path.endswith('.xz'):
        opener = lzma.open
    elif path.endswith('.gz'):
        opener = gzip.open
    with opener(path, 'rt', encoding='utf-8') as handle:
        return json.load(handle)


def dyck_words(a):
    words = []

    def rec(prefix, opened, closed):
        if opened == a and closed == a:
            words.append(prefix)
            return
        if opened < a:
            rec(prefix + 'L', opened + 1, closed)
        if closed < opened:
            rec(prefix + 'U', opened, closed + 1)

    rec('', 0, 0)
    return words


def compositions_upto(d, total):
    """All x in Z_{>=0}^d with sum(x) <= total."""
    if d == 0:
        yield ()
        return
    for first in range(total + 1):
        for rest in compositions_upto(d - 1, total - first):
            yield (first,) + rest


def boundaries(word, x):
    """Lower/upper boundaries L_i, U_i and b from an endpoint word and gaps."""
    a = len(word) // 2
    position = x[0]
    lows, ups = [], []
    for index, letter in enumerate(word):
        (lows if letter == 'L' else ups).append(position)
        position += x[index + 1]
    return tuple(lows), tuple(ups), position


def active_counts(word):
    """Number of short-chain elements incomparable with each gap segment."""
    counts = [0]
    opened = closed = 0
    for letter in word:
        if letter == 'L':
            opened += 1
        else:
            closed += 1
        counts.append(opened - closed)
    counts[-1] = 0
    return counts


def omega_values(a, b, lows, ups):
    """Omega_P(m) for m = 0..a+b, by multichains of ideals.

    Elements A_1<...<A_a and B_1<...<B_b; B_j < A_i iff j <= L_i and
    A_i < B_j iff j > U_i.  The ideals are the prefix pairs (i, j) with
    (i == 0 or L_i <= j) and (i == a or U_{i+1} >= j).
    """
    n = a + b
    valid = [[(i == 0 or lows[i - 1] <= j) and (i == a or ups[i] >= j)
              for j in range(b + 1)] for i in range(a + 1)]
    # N[i][j] = number of weak maps to [m] of the ideal (i, j) (if valid)
    count = [[1 if (valid[i][j] and i == 0 and j == 0) else 0
              for j in range(b + 1)] for i in range(a + 1)]
    values = [count[a][b]]
    for _ in range(n):
        new = [[0] * (b + 1) for _ in range(a + 1)]
        for i in range(a + 1):
            for j in range(b + 1):
                s = count[i][j]
                if i:
                    s += new[i - 1][j]
                if j:
                    s += new[i][j - 1]
                if i and j:
                    s -= new[i - 1][j - 1]
                new[i][j] = s
        # new[i][j] is the 2D prefix sum; keep only valid ideals
        count = [[new[i][j] if valid[i][j] else 0 for j in range(b + 1)]
                 for i in range(a + 1)]
        values.append(count[a][b])
    return values


def linear_coefficient(values):
    """[t] of the degree-n polynomial with the given values at 0..n."""
    diffs = list(values)
    total = Fraction(0)
    for k in range(1, len(values)):
        diffs = [diffs[i + 1] - diffs[i] for i in range(len(diffs) - 1)]
        total += Fraction((-1) ** (k - 1) * diffs[0], k)
    return total


def check_poset_order(a, b, lows, ups):
    """Sanity: the boundary data define a partial order (transitive closure)."""
    elems = [('A', i) for i in range(1, a + 1)] + [('B', j) for j in range(1, b + 1)]

    def less(p, q):
        if p[0] == q[0]:
            return p[1] < q[1]
        if p[0] == 'B':
            return p[1] <= lows[q[1] - 1]
        return q[1] > ups[p[1] - 1]

    for p in elems:
        if less(p, p):
            return False
        for q in elems:
            if less(p, q) and less(q, p):
                return False
            if less(p, q):
                for r in elems:
                    if less(q, r) and not less(p, r):
                        return False
    return True


_cache = {}


def true_value(a, word, x):
    lows, ups, b = boundaries(word, x)
    if b == 0:
        return Fraction(0)
    key = (a, lows, ups, b)
    if key not in _cache:
        c1 = linear_coefficient(omega_values(a, b, lows, ups))
        _cache[key] = c1 * math.factorial(a + b) / math.factorial(b - 1)
    return _cache[key]


def parse_poly(terms, dim):
    poly = {}
    for term in terms:
        exps = tuple(term['exponents'])
        if len(exps) != dim or any((not isinstance(e, int)) or e < 0 for e in exps):
            raise ValueError('bad exponent vector')
        if exps in poly:
            raise ValueError('duplicate monomial')
        coef = Fraction(term['coefficient'])
        if coef == 0:
            raise ValueError('explicit zero coefficient')
        poly[exps] = coef
    return poly


def add_term(poly, exps, coef):
    value = poly.get(exps, 0) + coef
    if value:
        poly[exps] = value
    else:
        poly.pop(exps, None)


def vec_add(*vectors):
    return tuple(sum(entries) for entries in zip(*vectors))


def evaluate_grouped(poly, points):
    """Evaluate poly at integer points, grouping monomials by support."""
    supports = {}
    for exps, coef in poly.items():
        mask = 0
        for index, e in enumerate(exps):
            if e:
                mask |= 1 << index
        supports.setdefault(mask, []).append((exps, coef))
    by_mask = {}
    for x in points:
        mask = 0
        for index, e in enumerate(x):
            if e:
                mask |= 1 << index
        by_mask.setdefault(mask, []).append(x)
    result = {}
    for mask, pts in by_mask.items():
        relevant = [item for sub, items in supports.items() if sub & ~mask == 0
                    for item in items]
        for x in pts:
            total = Fraction(0)
            for exps, coef in relevant:
                term = coef
                for index, e in enumerate(exps):
                    if e:
                        term *= x[index] ** e
                total += term
            result[x] = total
    return result


def check_chamber(a, word, poly, nonneg_part, extra, rng, report):
    dim = 2 * a + 1
    if any(sum(e) > a for e in poly):
        raise ValueError(f'{word}: degree exceeds {a}')
    if tuple([0] * dim) in poly:
        raise ValueError(f'{word}: nonzero constant term')
    points = list(compositions_upto(dim, a))
    values = evaluate_grouped(poly, points)
    for x in points:
        if values[x] != true_value(a, word, x):
            raise ValueError(f'{word}: mismatch at {x}')
    report['points'] += len(points)
    # quantitative bound: degree-one coefficients of the nonnegative part
    counts = active_counts(word)
    for j in range(dim):
        unit = tuple(1 if k == j else 0 for k in range(dim))
        expected = math.factorial(a - 1) if counts[j] < a else 0
        if nonneg_part.get(unit, 0) != expected:
            raise ValueError(f'{word}: degree-one coefficient of x_{j}')
        report['linear_coefficients'] += 1
    # out-of-sample points with |x| > a
    for _ in range(extra):
        total = rng.randint(a + 1, a + 8)
        cuts = sorted(rng.randint(0, total) for _ in range(dim - 1))
        x = tuple(hi - lo for lo, hi in zip([0] + cuts, cuts + [total]))
        lows, ups, b = boundaries(word, x)
        if not check_poset_order(a, b, lows, ups):
            raise ValueError('boundary data not a partial order')
        value = sum(coef * math.prod(x[i] ** e for i, e in enumerate(exps))
                    for exps, coef in poly.items())
        if value != true_value(a, word, x):
            raise ValueError(f'{word}: out-of-sample mismatch at {x}')
        report['extra_points'] += 1


def check_gap_record(a, record, extra, rng, report):
    """Check one square certificate (a = 4, 5) completely."""
    dim = 2 * a + 1
    word = record['endpoint_word']
    poly = parse_poly(record['polynomial'], dim)
    residual = parse_poly(record['residual'], dim)
    if any(c < 0 for c in residual.values()):
        raise ValueError(f'{word}: negative remainder coefficient')
    rebuilt = dict(residual)
    for sq in record['squares']:
        weight, ratio = Fraction(sq['weight']), Fraction(sq['ratio'])
        m, u, v = (tuple(sq[k]) for k in ('multiplier', 'u', 'v'))
        if weight < 0 or any(len(t) != dim or min(t) < 0 for t in (m, u, v)):
            raise ValueError(f'{word}: bad square')
        add_term(rebuilt, vec_add(m, u, u), weight * ratio * ratio)
        add_term(rebuilt, vec_add(m, u, v), -2 * weight * ratio)
        add_term(rebuilt, vec_add(m, v, v), weight)
    if rebuilt != poly:
        raise ValueError(f'{word}: squares + remainder != polynomial')
    check_chamber(a, word, poly, residual, extra, rng, report)


def controls(record):
    """Corrupted certificates that must be rejected."""
    import copy
    results = {}
    dim = len(record['polynomial'][0]['exponents'])
    a = (dim - 1) // 2
    scratch = {'points': 0, 'linear_coefficients': 0, 'extra_points': 0}

    def rejected(bad):
        try:
            check_gap_record(a, bad, 0, random.Random(0), dict(scratch))
        except ValueError:
            return True
        return False

    # add x_0^2 to polynomial and remainder: a valid square identity for the
    # wrong polynomial, which only the point identities can detect
    bad = copy.deepcopy(record)
    key = [2] + [0] * (dim - 1)
    for field in ('polynomial', 'residual'):
        for term in bad[field]:
            if term['exponents'] == key:
                term['coefficient'] = str(Fraction(term['coefficient']) + 1)
                break
        else:
            bad[field].append({'exponents': key, 'coefficient': '1'})
    results['shifted_polynomial_and_remainder'] = rejected(bad)
    bad = copy.deepcopy(record)
    bad['squares'][0]['weight'] = str(-Fraction(bad['squares'][0]['weight']))
    results['negative_square_weight'] = rejected(bad)
    bad = copy.deepcopy(record)
    bad['squares'][0]['weight'] = str(2 * Fraction(bad['squares'][0]['weight']))
    results['wrong_square_weight'] = rejected(bad)
    if not all(results.values()):
        raise ValueError('a corrupted certificate was accepted: ' + json.dumps(results))
    return results


def main():
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--short3', default=str(DATA / 'SHORT_CHAIN_CERTIFICATE.json.xz'))
    parser.add_argument('--gap4', default=str(DATA / 'GAP_SOS_A4.json.xz'))
    parser.add_argument('--gap5', default=str(DATA / 'GAP_SOS_A5.json.xz'))
    parser.add_argument('--extra', type=int, default=0,
                        help='random out-of-sample points per chamber')
    parser.add_argument('--seed', type=int, default=20261031)
    parser.add_argument('--json', help='write the report to this file')
    args = parser.parse_args()
    started = time.monotonic()
    rng = random.Random(args.seed)
    report = {'chambers': 0, 'points': 0, 'squares': 0, 'linear_coefficients': 0,
              'extra_points': 0, 'per_size': {}}

    short = load(args.short3)
    seen = {}
    for cert in short['certificates']:
        a, word = cert['a'], cert['endpoint_word']
        if cert['variables'] != 2 * a + 1 or cert['degree_bound'] != a:
            raise ValueError('short certificate header')
        poly = parse_poly(cert['coefficients'], 2 * a + 1)
        if any(c <= 0 or c.denominator != 1 for c in poly.values()):
            raise ValueError(f'{word}: coefficient not a positive integer')
        if (a, word) in seen:
            raise ValueError('duplicate chamber')
        seen[(a, word)] = poly
    for a in (1, 2, 3):
        if sorted(w for (s, w) in seen if s == a) != sorted(dyck_words(a)):
            raise ValueError(f'chamber set incomplete for a={a}')
    for (a, word), poly in sorted(seen.items()):
        before = report['points']
        check_chamber(a, word, poly, poly, args.extra, rng, report)
        report['chambers'] += 1
        size = report['per_size'].setdefault(str(a), {'chambers': 0, 'points': 0, 'squares': 0})
        size['chambers'] += 1
        size['points'] += report['points'] - before

    for path, a in ((args.gap4, 4), (args.gap5, 5)):
        data = load(path)
        if data['a'] != a:
            raise ValueError('wrong size in ' + path)
        dim = 2 * a + 1
        words = [r['endpoint_word'] for r in data['records']]
        if sorted(words) != sorted(dyck_words(a)) or len(set(words)) != len(words):
            raise ValueError(f'chamber set incomplete for a={a}')
        size = report['per_size'].setdefault(str(a), {'chambers': 0, 'points': 0, 'squares': 0})
        for record in data['records']:
            before = report['points']
            check_gap_record(a, record, args.extra, rng, report)
            report['chambers'] += 1
            report['squares'] += len(record['squares'])
            size['chambers'] += 1
            size['squares'] += len(record['squares'])
            size['points'] += report['points'] - before
        if a == 4:
            report['negative_controls'] = controls(data['records'][0])
    report['distinct_posets_evaluated'] = len(_cache)
    report['examples'] = examples()
    report['seconds'] = round(time.monotonic() - started, 1)
    report['status'] = 'PASS'
    text = json.dumps(report, indent=2, sort_keys=True)
    if args.json:
        Path(args.json).write_text(text + '\n')
    print(text)


def examples():
    """The worked examples of the manuscript, recomputed from scratch."""
    cases = [
        ('a=1, b=8, L=2, U=6', 1, 8, (2,), (6,), Fraction(1, 18)),
        ('a=5, b=20, L=(0,2,5,5,11), U=(4,8,12,17,20)', 5, 20, (0, 2, 5, 5, 11),
         (4, 8, 12, 17, 20), Fraction(7123, 531300)),
        ('a=5, b=20, no cross-comparability', 5, 20, (0,) * 5, (20,) * 5, Fraction(0)),
    ]
    out = []
    for label, a, b, lows, ups, expected in cases:
        if not check_poset_order(a, b, lows, ups):
            raise ValueError('example is not a partial order')
        value = linear_coefficient(omega_values(a, b, lows, ups))
        if value != expected:
            raise ValueError('example value differs: ' + label)
        out.append({'example': label, 'linear_coefficient': str(value)})
    return out


if __name__ == '__main__':
    try:
        main()
    except ValueError as error:
        print(json.dumps({'status': 'FAIL', 'error': str(error)}))
        sys.exit(1)
