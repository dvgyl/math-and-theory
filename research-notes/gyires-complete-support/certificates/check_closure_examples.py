#!/usr/bin/env python3
"""Check the two closure examples with exact rational arithmetic."""

from fractions import Fraction as F
from itertools import permutations
from math import factorial, prod
from pathlib import Path
import json


def permanent(matrix):
    n = len(matrix)
    return sum(
        (prod(matrix[i][p[i]] for i in range(n)) for p in permutations(range(n))),
        F(0),
    )


def product_polynomial(matrix):
    n = len(matrix[0])
    polynomial = {(0,) * n: F(1)}
    for row in matrix:
        updated = {}
        for powers, coefficient in polynomial.items():
            for j, entry in enumerate(row):
                key = list(powers)
                key[j] += 1
                key = tuple(key)
                updated[key] = updated.get(key, F(0)) + coefficient * entry
        polynomial = updated
    return polynomial


def extract(polynomial, column, exponent):
    return {
        powers[:column] + powers[column + 1 :]: coefficient
        for powers, coefficient in polynomial.items()
        if powers[column] == exponent
    }


def norm(polynomial):
    return sum(
        (prod(factorial(k) for k in powers) * coefficient**2
         for powers, coefficient in polynomial.items()),
        F(0),
    )


def gram(matrix):
    return [[sum((a * b for a, b in zip(row, other)), F(0))
             for other in matrix] for row in matrix]


def det3(matrix):
    a = matrix
    return (a[0][0] * (a[1][1] * a[2][2] - a[1][2] * a[2][1])
            - a[0][1] * (a[1][0] * a[2][2] - a[1][2] * a[2][0])
            + a[0][2] * (a[1][0] * a[2][1] - a[1][1] * a[2][0]))


def check_matrix(matrix):
    n = len(matrix)
    assert all(value >= 0 for row in matrix for value in row)
    assert all(sum(row) == 1 for row in matrix)
    assert all(sum(matrix[i][j] for i in range(n)) == 1 for j in range(n))
    assert det3(matrix) == 0
    assert any(matrix[i][j] * matrix[k][ell] != matrix[i][ell] * matrix[k][j]
               for i in range(n) for k in range(i + 1, n)
               for j in range(n) for ell in range(j + 1, n))


def main():
    a = [[F(value, 1500) for value in row]
         for row in [[482, 725, 293], [478, 775, 247], [540, 0, 960]]]
    check_matrix(a)
    polynomial = product_polynomial(a)
    assert norm(polynomial) == permanent(gram(a))
    q = extract(polynomial, 0, 1)
    assert q == {(2, 0): F(899, 10000), (1, 1): F(303539, 1125000),
                 (0, 2): F(4797067, 56250000)}
    h = q[1, 1]**2 + 4 * q[2, 0] * q[0, 2]
    g3 = F(2, 3)**2
    difference = g3 * norm(polynomial) - h
    ratio = h / (g3 * norm(polynomial))
    assert difference == F(4550848849393, 1186523437500000) > 0
    assert ratio == F(122764681516875, 127315530366268) < 1

    b = [[F(1, 2), F(1, 4), F(1, 4)],
         [F(1, 2), F(1, 4), F(1, 4)],
         [F(0), F(1, 2), F(1, 2)]]
    check_matrix(b)
    bp = product_polynomial(b)
    coefficients = [factorial(k) * norm(extract(bp, 0, k)) for k in range(4)]
    assert coefficients == [F(3, 64), F(1, 8), F(1, 16), F(0)]
    bg = gram(b)
    for z in map(F, [0, 1, 2, 3]):
        matrix = [[bg[i][j] + (z - 1) * b[i][0] * b[j][0]
                   for j in range(3)] for i in range(3)]
        assert permanent(matrix) == sum(c * z**k for k, c in enumerate(coefficients))
    for root in [F(-1, 2), F(-3, 2)]:
        assert sum(c * root**k for k, c in enumerate(coefficients)) == 0
    mean = sum(k * c for k, c in enumerate(coefficients)) / sum(coefficients)
    assert mean == F(16, 15)
    report = {
        "arithmetic": "fractions.Fraction, direct permutation permanent",
        "all_checks_passed": True,
        "every_column_deletion_counterexample": {
            "matrix_rank": 2, "doubly_stochastic": True,
            "deleted_column_one_based": 1, "zero_column_one_based": 2,
            "coefficients_a_b_c": [str(q[key]) for key in [(2, 0), (1, 1), (0, 2)]],
            "g3_N_minus_H": str(difference), "H_over_g3_N": str(ratio),
        },
        "collision_example": {
            "matrix_rank": 2, "doubly_stochastic": True,
            "coefficients_by_degree": [str(c) for c in coefficients],
            "direct_gram_permanent_evaluations": 4,
            "roots": ["-1/2", "-3/2"], "mean": str(mean),
        },
    }
    destination = Path(__file__).with_name("closure_examples_verification.json")
    destination.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
