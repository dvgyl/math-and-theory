from collections import Counter
from fractions import Fraction
from itertools import permutations
from math import factorial
from pathlib import Path
import json


def permanent(matrix):
    n = len(matrix)
    total = 0
    for order in permutations(range(n)):
        term = 1
        for i, j in enumerate(order):
            term *= matrix[i][j]
        total += term
    return total


def coefficient_power(terms, n):
    result = {(0, 0): 1}
    for _ in range(n):
        expanded = Counter()
        for (i, j), a in result.items():
            for (k, r), b in terms.items():
                if i + k <= n and j + r <= n:
                    expanded[i + k, j + r] += a * b
        result = expanded
    return result


def formula(n, d, second_moment=False):
    if second_moment:
        terms = {(1, 0): d, (0, 1): d * (d - 1)}
    else:
        terms = {
            (k, r): factorial(d) * factorial(k + r)
            // (factorial(k) * factorial(r) ** 2 * factorial(d - k - 2 * r))
            for k in range(d + 1)
            for r in range((d - k) // 2 + 1)
        }
    power = coefficient_power(terms, n)
    total = sum(
        (d - 1) ** (n - t) * factorial((d - 2) * n + t)
        * factorial(n - t) * power.get((t, n - t), 0)
        for t in range(n + 1)
    )
    return Fraction(factorial(n) * d ** n * total, factorial(d * n))


records = []
for n, d in [(1, 2), (1, 3), (1, 4), (2, 2), (2, 3), (3, 2), (4, 2)]:
    gram_total = 0
    square_total = 0
    count = 0
    for assignment in permutations(range(n * d)):
        matrix = [[0] * n for _ in range(n)]
        for row_stub, column_stub in enumerate(assignment):
            matrix[row_stub // d][column_stub // d] += 1
        gram = [[sum(matrix[i][k] * matrix[j][k] for k in range(n))
                 for j in range(n)] for i in range(n)]
        gram_total += permanent(gram)
        square_total += permanent(matrix) ** 2
        count += 1
    assert count == factorial(n * d)
    expected_gram = formula(n, d)
    expected_square = formula(n, d, True)
    assert Fraction(gram_total, count) == expected_gram
    assert Fraction(square_total, count) == expected_square
    records.append(dict(n=n, d=d, bijections=count,
                        gram_expectation=str(expected_gram),
                        permanent_second_moment=str(expected_square)))
    print(records[-1], flush=True)
output = Path(__file__).with_suffix('.json')
output.write_text(json.dumps(dict(status='PASS', cases=records), indent=2) + '\n')
