#!/usr/bin/env python3
"""Exact finite checks of two proposed power-rank formulae.

Run: python check_original.py --max-power 40
Requires Python 3.10+; standard library only.

These are reproducible integer-arithmetic checks, NOT Lean verification and
NOT a substitute for the all-powers arguments in the accompanying manuscript.
"""
from __future__ import annotations

if not __debug__:
    raise SystemExit("Optimization disables required arithmetic checks; run without -O, -OO, or PYTHONOPTIMIZE.")

import argparse
import json
from collections import defaultdict
from fractions import Fraction
from math import comb, isqrt
from pathlib import Path

Monomial = tuple[int, int, int]
Polynomial = dict[Monomial, int]

# Monomials are (X exponent, Y exponent, Z exponent).
# F = 1 + X + Y(1-X)^2 + Z Y^2 (1+X)^3.
BASE: Polynomial = {
    (0, 0, 0): 1, (1, 0, 0): 1,
    (0, 1, 0): 1, (1, 1, 0): -2, (2, 1, 0): 1,
    (0, 2, 1): 1, (1, 2, 1): 3,
    (2, 2, 1): 3, (3, 2, 1): 1,
}


def square_count(m: int) -> int:
    if m < 1:
        raise ValueError("The power must be positive.")
    return sum(
        m < q*q < 3*m and (q*q - m) % 2 == 1
        for q in range(isqrt(3*m) + 1)
    )


def predicted_rank(m: int) -> int:
    q = square_count(m)
    numerator = (m+1)*(2*m+1)*(7*m+6)
    assert numerator % 6 == 0
    return numerator // 6 - 2*q


def multiply_base(polynomial: Polynomial) -> Polynomial:
    result: defaultdict[Monomial, int] = defaultdict(int)
    for (i, j, k), a in polynomial.items():
        for (ii, jj, kk), b in BASE.items():
            result[i+ii, j+jj, k+kk] += a*b
    return {monomial: coefficient for monomial, coefficient in result.items()
            if coefficient != 0}


def exponential_rank(polynomial: Polynomial) -> int:
    """Sum degree_Z+1 after grouping by X,Y.

    Its interpretation as recurrence rank uses the rank lemma proved in the
    accompanying note and multiplicative independence of 2 and 3.
    """
    degrees: dict[tuple[int, int], int] = {}
    for (i, j, k), coefficient in polynomial.items():
        if coefficient != 0:
            degrees[i, j] = max(degrees.get((i, j), -1), k)
    return sum(degree + 1 for degree in degrees.values())


def family_rank(d: int, m: int) -> int:
    return len({a+d*b for b in range(m+1) for a in range(m-b+1)})


def family_formula(d: int, m: int) -> int:
    if d < 2 or m < 1:
        raise ValueError("Require d >= 2 and m >= 1.")
    if m <= d-1:
        return comb(m+2, 2)
    return d*m + 1 - (d-1)*(d-2)//2


def binomial(n: int, k: int) -> int:
    return comb(n, k) if 0 <= k <= n else 0


def signed_coefficient(n: int, r: int, k: int) -> int:
    """[X^k](1-X)^r (1+X)^(n-r), by direct expansion."""
    return sum((-1)**i * comb(r, i) * binomial(n-r, k-i)
               for i in range(r+1))


def check_coefficient_identities(limit: int = 100) -> dict[str, int]:
    quadratic_checks = 0
    sixth_checks = 0
    for n in range(2, limit+1):
        for k in range(n+1):
            expected = Fraction(comb(n, k)*((n-2*k)**2-n), n*(n-1))
            actual = signed_coefficient(n, 2, k)
            assert actual == expected, ("quadratic", n, k, actual, expected)
            quadratic_checks += 1
        q = isqrt(n)
        if n >= 6 and q*q == n:
            for k in ((n-q)//2, (n+q)//2):
                expected = Fraction(comb(n, k)*16, (n-2)*(n-3)*(n-5))
                actual = signed_coefficient(n, 6, k)
                assert actual == expected, ("sixth", n, k, actual, expected)
                assert actual > 0
                sixth_checks += 1
    return {"quadratic_coefficient_checks": quadratic_checks,
            "sixth_coefficient_checks_at_squares": sixth_checks,
            "maximum_N": limit}


def main(limit: int, output: Path) -> None:
    if limit < 1:
        raise ValueError("--max-power must be positive.")
    polynomial: Polynomial = {(0, 0, 0): 1}
    rows: list[dict[str, int]] = []
    for m in range(1, limit+1):
        polynomial = multiply_base(polynomial)
        actual = exponential_rank(polynomial)
        expected = predicted_rank(m)
        assert actual == expected, ("rank13", m, actual, expected)
        row = {
            "power": m, "rank": actual,
            "baseline": (m+1)*(2*m+1)*(7*m+6)//6,
            "square_count": square_count(m),
            "nonzero_trivariate_coefficients": len(polynomial),
        }
        rows.append(row)
        if m <= 12 or m % 10 == 0:
            print(row, flush=True)

    for d in range(2, 31):
        for m in range(1, 81):
            actual, expected = family_rank(d, m), family_formula(d, m)
            assert actual == expected, ("rank3", d, m, actual, expected)

    coefficient_checks = check_coefficient_identities()
    data = {
        "verification_kind": "finite exact arithmetic; not a Lean proof",
        "max_power": limit, "checks": rows,
        "rank3_family_checks": 29*80,
        "rank3_d_range": [2, 30], "rank3_power_range": [1, 80],
        "coefficient_checks": coefficient_checks,
    }
    output.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    print(f"PASS: exact trivariate expansions, M = 1..{limit}")
    print("PASS: 2320 rank-3 support checks, d = 2..30, M = 1..80")
    print(f"PASS: coefficient identities: {coefficient_checks}")
    print(f"Results written to {output}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-power", type=int, default=40)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).with_name("exact_check_results.json"))
    args = parser.parse_args()
    main(args.max_power, args.output)
