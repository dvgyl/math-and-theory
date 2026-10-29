#!/usr/bin/env python3
"""Independent finite checks of the revised all-powers results.

Python 3.10+, standard library only. This program does not call Lean and its
finite computations are not a proof of the universally quantified theorems.
"""
from __future__ import annotations

if not __debug__:
    raise SystemExit("Optimization disables required arithmetic checks; run without -O, -OO, or PYTHONOPTIMIZE.")
import argparse
import json
from collections import defaultdict
from itertools import product
from math import comb, isqrt
from pathlib import Path
from time import perf_counter
from check_original import multiply_base, predicted_rank, square_count


def compositions(total: int, length: int):
    if length == 1:
        yield (total,)
    else:
        for first in range(total + 1):
            for tail in compositions(total-first, length-1):
                yield (first,) + tail


def general_formula(r: int, d: int, m: int) -> int:
    if r < 3 or d < 2 or m < 0:
        raise ValueError("Require r >= 3, d >= 2, M >= 0")
    return comb(m+r-1, r-1) - (comb(m-d+r-1, r-1) if m >= d else 0)


def actual_support(r: int, d: int, m: int):
    # Coordinates are exponents of 2 and the r-3 independent odd primes.
    return {(b[1]+d*b[2],) + b[3:] for b in compositions(m, r)}


def normal_form(b: tuple[int, ...], d: int):
    q, a = divmod(b[1], d)
    return (b[0]+(d-1)*q, a, b[2]+q) + b[3:]


def square_count_floor(m: int) -> int:
    if m < 1:
        raise ValueError("M must be positive")
    eps = m % 2
    lower, upper = isqrt(m), isqrt(3*m-1)
    return (upper+1-eps)//2 - (lower+1-eps)//2


def multiplicities_formula(m: int) -> dict[tuple[int, int], int]:
    result = {}
    for j in range(2*m+1):
        n = m+j
        for k in range(n+1):
            loss = int(j % 2 == 1 and (n-2*k)**2 == n)
            multiplicity = j//2+1-loss
            if multiplicity:
                result[k, j] = multiplicity
    return result


def multiplicities_expansion(poly):
    result = {}
    for (k, j, a), coefficient in poly.items():
        if coefficient:
            result[k, j] = max(a+1, result.get((k,j), 0))
    return result


def berlekamp_massey(values: list[int], prime: int) -> list[int]:
    """C[0]=1; sum(C[i]*values[n-i], i=0..L)=0 after the prefix."""
    c, b = [1], [1]
    length, offset, last = 0, 1, 1
    for n, value in enumerate(values):
        discrepancy = (value + sum(c[i]*values[n-i]
                                  for i in range(1, length+1))) % prime
        if discrepancy == 0:
            offset += 1
            continue
        old = c[:]
        scale = discrepancy * pow(last, -1, prime) % prime
        if len(c) < len(b)+offset:
            c.extend([0]*(len(b)+offset-len(c)))
        for j, value_b in enumerate(b):
            c[j+offset] = (c[j+offset] - scale*value_b) % prime
        if 2*length <= n:
            length = n+1-length
            b, last, offset = old, discrepancy, 1
        else:
            offset += 1
    return c[:length+1]


def s_values_mod(power: int, length: int, prime: int) -> list[int]:
    result = []
    a, b, c = 1, 1, 1
    for n in range(length):
        sn = (1+a+b*(1-a)**2+n*c*(1+a)**3) % prime
        result.append(pow(sn, power, prime))
        a, b, c = 2*a % prime, 3*b % prime, 9*c % prime
    return result


def charpoly_descending_mod(m: int, prime: int) -> list[int]:
    # Start with 1 and multiply (T-root) once per multiplicity.
    coeff = [1]
    for (k, j), multiplicity in multiplicities_formula(m).items():
        root = pow(2, k, prime)*pow(3, j, prime) % prime
        for _ in range(multiplicity):
            new = [0]*(len(coeff)+1)
            for i, v in enumerate(coeff):
                new[i] = (new[i]+v) % prime
                new[i+1] = (new[i+1]-root*v) % prime
            coeff = new
    return coeff


def main(max_power: int, max_bm: int, output: Path) -> None:
    start = perf_counter()
    general_checks = normal_checks = 0
    for r in range(3, 8):
        for d in range(2, 13):
            for m in range(0, 13):
                support = actual_support(r, d, m)
                expected = general_formula(r,d,m)
                assert len(support) == expected, (r,d,m,len(support),expected)
                canonical = set()
                for b in compositions(m, r):
                    normal = normal_form(b, d)
                    assert sum(normal) == m and normal[1] < d
                    assert normal[1]+d*normal[2] == b[1]+d*b[2]
                    assert normal[3:] == b[3:]
                    canonical.add(normal)
                    normal_checks += 1
                assert len(canonical) == len(support)
                general_checks += 1
    print(f"PASS: {general_checks} general-family support cases; "
          f"{normal_checks} normal-form reductions", flush=True)

    floor_checks = 20000
    for m in range(1, floor_checks+1):
        assert square_count_floor(m) == square_count(m), m
    print(f"PASS: {floor_checks} exact floor-count identities", flush=True)

    poly = {(0,0,0): 1}
    multiplicity_rows = []
    for m in range(1, max_power+1):
        poly = multiply_base(poly)
        actual = multiplicities_expansion(poly)
        expected = multiplicities_formula(m)
        assert actual == expected, (m, set(actual.items())^set(expected.items()))
        rank = sum(actual.values())
        assert rank == predicted_rank(m)
        multiplicity_rows.append({"power":m, "rank":rank,
                                  "distinct_bases":len(actual),
                                  "square_count":square_count_floor(m)})
    print(f"PASS: every root multiplicity, exact expansions M=1..{max_power}", flush=True)

    bm_rows = []
    for prime in (1000000007, 1000000009):
        for m in range(1, max_bm+1):
            rank = predicted_rank(m)
            values = s_values_mod(m, 2*rank+32, prime)
            connection = berlekamp_massey(values, prime)
            expected = charpoly_descending_mod(m, prime)
            assert connection == expected, (prime,m,len(connection)-1,rank)
            bm_rows.append({"prime":prime,"power":m,"linear_complexity":len(connection)-1,
                            "samples":len(values),"characteristic_polynomial_matches":True})
            print(f"PASS: direct sequence BM, p={prime}, M={m}, rank={rank}", flush=True)
    data = {
        "scope":"Finite checks only; NOT Lean verification or a proof for all powers.",
        "general_family":{"r_range":[3,7],"d_range":[2,12],"M_range":[0,12],
                          "support_cases":general_checks,"normal_form_checks":normal_checks},
        "floor_count_checks":floor_checks,
        "full_multiplicity_checks":multiplicity_rows,
        "independent_modular_BM_checks":bm_rows,
        "elapsed_seconds":round(perf_counter()-start,3),
    }
    output.write_text(json.dumps(data,indent=2)+"\n")
    print(f"All checks passed; results: {output}", flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-power',type=int,default=30)
    parser.add_argument('--max-bm',type=int,default=8)
    parser.add_argument('--output',type=Path,default=Path(__file__).with_name('revision_checks.json'))
    args=parser.parse_args()
    if args.max_power < 1 or args.max_bm < 1:
        parser.error('Both limits must be positive')
    main(args.max_power,args.max_bm,args.output)
