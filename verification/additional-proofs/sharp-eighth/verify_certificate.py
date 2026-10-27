#!/usr/bin/env python3
"""Independent exact-rational check of the finite certificate data.

Python standard library only. This supplements, and does not replace, the
Lean proof that interprets the certificate in every cube dimension.
"""

if not __debug__:
    raise SystemExit("Run this verifier without Python optimization.")
from collections import Counter, defaultdict
from fractions import Fraction as Q
from math import comb, factorial, prod
from pathlib import Path
import json
import re

HERE = Path(__file__).resolve().parent


def reject_number(value):
    raise ValueError("Use integers or rational strings, not JSON decimal numbers.")


def unique_object(items):
    result = {}
    for key, value in items:
        if key in result:
            raise ValueError("Duplicate JSON field: " + key)
        result[key] = value
    return result


def exact_json(path):
    return json.loads(path.read_text(), parse_float=reject_number,
                      parse_constant=reject_number, object_pairs_hook=unique_object)


def rational(value):
    if type(value) is not str or not re.fullmatch(r"-?(?:0|[1-9][0-9]*)(?:/[1-9][0-9]*)?", value):
        raise ValueError("A rational coefficient must be an integer or fraction string.")
    return Q(value)


data = exact_json(HERE / "exact_certificate.json")
uni = exact_json(HERE / "univariate_certificate.json")
assert type(data) is dict and set(data) == {"M", "coefficients", "terms", "threshold", "expected_bound"}
assert type(data["M"]) is int and data["M"] == 9
assert type(data["coefficients"]) is list and len(data["coefficients"]) == 10
assert type(data["terms"]) is list and len(data["terms"]) == 28
assert rational(data["threshold"]) == Q(9, 4)
assert rational(data["expected_bound"]) == Q(3, 16)
for coefficient in data["coefficients"]:
    rational(coefficient)
for entry in data["terms"]:
    assert type(entry) is list and len(entry) == 2
    descriptor, weight = entry
    rational(weight)
    assert type(descriptor) is list and len(descriptor) >= 2
    kind, lam, *tail = descriptor
    assert type(lam) is list and lam and all(type(a) is int and a > 0 for a in lam)
    if kind == "monomial":
        assert len(descriptor) == 2 and sum(lam) == 9
    elif kind == "square":
        assert len(descriptor) == 3 and sum(lam) == 7
        assert type(tail[0]) is list and len(tail[0]) == len(lam) + 1
        assert all(type(a) is int for a in tail[0])
    elif kind == "highsquare":
        assert len(descriptor) == 6 and sum(lam) == 7
        i, j, a, b = tail
        assert all(type(v) is int for v in tail)
        assert 0 <= i < len(lam) and 0 <= j < len(lam)
    else:
        raise ValueError("Unknown term kind.")
assert type(uni) is list and len(uni) == 2
assert all(type(item) is dict and set(item) ==
           {"name", "polynomial", "tail_start", "tail_coefficients", "intervals"} for item in uni)
assert sorted(item["name"] for item in uni) == ["R", "T"]
for item in uni:
    degree, intervals = (7, 5) if item["name"] == "R" else (16, 11)
    for key in ("polynomial", "tail_coefficients"):
        assert type(item[key]) is list and len(item[key]) == degree + 1
        for coefficient in item[key]:
            rational(coefficient)
    rational(item["tail_start"])
    assert type(item["intervals"]) is list and len(item["intervals"]) == intervals
    for row in item["intervals"]:
        assert type(row) is dict and set(row) == {"lo", "hi", "bernstein"}
        rational(row["lo"])
        rational(row["hi"])
        assert type(row["bernstein"]) is list and len(row["bernstein"]) == degree + 1
        for coefficient in row["bernstein"]:
            rational(coefficient)
p = [Q(x) for x in data["coefficients"]]
assert data["M"] == 9 and len(p) == 10
assert Q(data["threshold"]) == Q(9, 4)
assert Q(data["expected_bound"]) == Q(3, 16)


def canon(xs):
    return tuple(sorted(xs, reverse=True))


def aut(xs):
    return prod(factorial(k) for k in Counter(xs).values())


def parts(n, cap=None):
    if n == 0:
        yield ()
        return
    if cap is None:
        cap = n
    for a in range(min(cap, n), 0, -1):
        for rest in parts(n - a, a):
            yield (a,) + rest


def add_scaled(dst, src, scale):
    for key, value in src.items():
        dst[key] += scale * value


def orbit(xs):
    return {canon(xs): Q(aut(xs))}


def mul_v(poly):
    """Multiply a polynomial in the monomial-symmetric basis by sum(z_i)."""
    out = defaultdict(Q)
    for lam, coefficient in poly.items():
        raised = [lam + (1,)]
        for i in range(len(lam)):
            q = list(lam)
            q[i] += 1
            raised.append(tuple(q))
        for q in raised:
            out[canon(q)] += coefficient * Q(aut(q), aut(lam))
    return dict(out)


def mul_v_power(poly, k):
    for _ in range(k):
        poly = mul_v(poly)
    return poly


def square_poly(lam, aa, b):
    out = defaultdict(Q)
    for i, a in enumerate(aa):
        for j, c in enumerate(aa):
            q = list(lam)
            q[i] += 1
            q[j] += 1
            add_scaled(out, orbit(q), a * c)
        q = list(lam)
        q[i] += 1
        add_scaled(out, mul_v(orbit(q)), 2 * b * a)
    add_scaled(out, mul_v_power(orbit(lam), 2), b * b)
    return dict(out)


gap = defaultdict(Q)
add_scaled(gap, mul_v_power({(): Q(1)}, 9), Q(3, 16))
for j, coefficient in enumerate(p):
    moment = {
        lam: Q(factorial(2 * j), prod(factorial(2 * a) for a in lam))
        for lam in parts(j)
    }
    add_scaled(gap, mul_v_power(moment, 9 - j), -coefficient * 3**j)

rhs = defaultdict(Q)
assert len(data["terms"]) == 28
for descriptor, weight_text in data["terms"]:
    weight = Q(weight_text)
    assert weight > 0
    kind, lam, *tail = descriptor
    assert all(isinstance(a, int) and a > 0 for a in lam)
    if kind == "monomial":
        assert sum(lam) == 9 and not tail
        term = {canon(lam): Q(1)}
    elif kind == "square":
        assert sum(lam) == 7
        aa_b = tail[0]
        assert len(aa_b) == len(lam) + 1
        term = square_poly(lam, aa_b[:-1], aa_b[-1])
    elif kind == "highsquare":
        assert sum(lam) == 7
        i, j, a, b = tail
        aa = [0] * len(lam)
        aa[i] += a
        aa[j] += b
        term = square_poly(lam, aa, 0)
    else:
        raise AssertionError(f"Unknown term kind: {kind}")
    add_scaled(rhs, term, weight)

all_parts = set(parts(9))
assert len(all_parts) == 30
assert set(gap).issubset(all_parts) and set(rhs).issubset(all_parts)
for lam in all_parts:
    assert gap[lam] == rhs[lam], (lam, gap[lam], rhs[lam])
print("PASS: all 30 symmetric coefficient identities and all 28 positive weights")


def trim(a):
    a = list(a)
    while len(a) > 1 and a[-1] == 0:
        a.pop()
    return a


def mul_poly(a, b):
    c = [Q(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            c[i + j] += x * y
    return trim(c)


def shift(a, start, scale=Q(1)):
    n = len(a) - 1
    return [
        sum(a[j] * comb(j, k) * start ** (j - k) * scale**k
            for j in range(k, n + 1))
        for k in range(n + 1)
    ]


def bernstein(a, lo, hi):
    c = shift(a, lo, hi - lo)
    n = len(a) - 1
    return [sum(c[k] * Q(comb(i, k), comb(n, k)) for k in range(i + 1))
            for i in range(n + 1)]


poly_x = [Q(0)] * 19
for j, a in enumerate(p):
    poly_x[2 * j] = a
hinge_difference = list(poly_x)
hinge_difference[0] += Q(9, 4)
hinge_difference[1] -= 1
assert {item["name"] for item in uni} == {"R", "T"}
total_intervals = 0
for item in uni:
    a = [Q(x) for x in item["polynomial"]]
    if item["name"] == "R":
        assert mul_poly([1, -2, 1], a) == trim(p)
    else:
        assert mul_poly([9, -6, 1], a) == trim(hinge_difference)
    start = Q(item["tail_start"])
    tail = [Q(x) for x in item["tail_coefficients"]]
    assert tail == shift(a, start) and all(x >= 0 for x in tail)
    intervals = sorted(item["intervals"], key=lambda row: Q(row["lo"]))
    endpoint = Q(0)
    for row in intervals:
        lo, hi = Q(row["lo"]), Q(row["hi"])
        assert lo == endpoint and hi > lo
        bc = [Q(x) for x in row["bernstein"]]
        assert bc == bernstein(a, lo, hi) and all(x >= 0 for x in bc)
        endpoint = hi
    assert endpoint == start
    total_intervals += len(intervals)
    print(f"PASS: {item['name']} exact factorization, {len(intervals)} Bernstein intervals, positive tail")
assert total_intervals == 16


def evaluate(a, x):
    return sum(c * x**i for i, c in enumerate(a))


derivative = [(i + 1) * poly_x[i + 1] for i in range(18)]
assert evaluate(poly_x, 1) == 0
assert evaluate(derivative, 1) == 0
assert evaluate(poly_x, 3) == Q(3, 4)
assert evaluate(derivative, 3) == 1
print("PASS: exact contacts P(1)=P'(1)=0, P(3)=3/4, P'(3)=1")
print("All finite certificate checks passed using rational arithmetic only.")
