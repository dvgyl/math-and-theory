#!/usr/bin/env python3
"""Independent exact-rational checks of the two finite witnesses.

These computations supplement the Lean proofs; they are not the formal verifier.
Run with Python 3, using only its standard library.
"""

from collections import Counter
from fractions import Fraction
from itertools import product
import json


def node(i, false_branch, true_branch):
    return (i, false_branch, true_branch)


def query(i):
    return node(i, False, True)


def evaluate(tree, assignment):
    if isinstance(tree, bool):
        return tree
    i, left, right = tree
    return evaluate(right if assignment[i] else left, assignment)


def sign(value):
    return 1 if value else -1


def counts(tree):
    if isinstance(tree, bool):
        return Counter()
    i, left, right = tree
    return Counter({i: 1}) + counts(left) + counts(right)


def regular(tree, ancestors=frozenset()):
    if isinstance(tree, bool):
        return True
    i, left, right = tree
    return i not in ancestors and regular(left, ancestors | {i}) and regular(right, ancestors | {i})


def average(values):
    return Fraction(sum(values), len(values))


def covariance(left, right, cube):
    g = [sign(evaluate(left, a)) for a in cube]
    h = [sign(evaluate(right, a)) for a in cube]
    return average([x * y for x, y in zip(g, h)]) - average(g) * average(h)


def tree_covariance(tree, cube):
    if isinstance(tree, bool):
        return Fraction(0)
    _, left, right = tree
    return covariance(left, right, cube) + (tree_covariance(left, cube) + tree_covariance(right, cube)) / 2


def every_query_relevant(tree, cube):
    if isinstance(tree, bool):
        return True
    _, left, right = tree
    return any(evaluate(left, a) != evaluate(right, a) for a in cube) and every_query_relevant(left, cube) and every_query_relevant(right, cube)


def four_variable_witness():
    left = node(0, False, node(3, query(1), query(1)))
    right = node(1, False, node(3, query(0), query(0)))
    return node(2, left, right)


def nine_variable_witness():
    rare_or = node(5, node(6, node(7, node(8, False, True), True), True), True)
    left = node(1, False, node(3, query(2), node(2, False, rare_or)))
    right = node(2, False, node(4, query(1), node(1, False, rare_or)))
    return node(0, left, right)


def check(tree, n, expected_counts, expected_mean, expected_variance, expected_covariance):
    cube = list(product([False, True], repeat=n))
    got_counts = [counts(tree)[i] for i in range(n)]
    got_mean = average([sign(evaluate(tree, a)) for a in cube])
    got_variance = covariance(tree, tree, cube)
    got_covariance = tree_covariance(tree, cube)
    if not (regular(tree)):
        raise ValueError('Mathematical check failed: regular(tree)')
    if not (got_counts == expected_counts):
        raise ValueError('Mathematical check failed: got_counts == expected_counts')
    if not (max(got_counts) == 3):
        raise ValueError('Mathematical check failed: max(got_counts) == 3')
    if not (got_mean == expected_mean):
        raise ValueError('Mathematical check failed: got_mean == expected_mean')
    if not (got_variance == expected_variance):
        raise ValueError('Mathematical check failed: got_variance == expected_variance')
    if not (got_covariance == expected_covariance):
        raise ValueError('Mathematical check failed: got_covariance == expected_covariance')
    return {
        "variables": n,
        "assignments_enumerated": len(cube),
        "counts": got_counts,
        "regular": True,
        "every_query_relevant": every_query_relevant(tree, cube),
        "mean": str(got_mean),
        "variance": str(got_variance),
        "tree_covariance": str(got_covariance),
    }


def main():
    small = four_variable_witness()
    robust = nine_variable_witness()
    first = check(small, 4, [3, 3, 1, 2], Fraction(-1, 2), Fraction(3, 4), Fraction(5, 4))
    second = check(robust, 9, [1, 3, 3, 1, 1, 2, 2, 2, 2], Fraction(-33, 64), Fraction(3007, 4096), Fraction(4863, 4096))
    if not (not first['every_query_relevant']):
        raise ValueError("Mathematical check failed: not first['every_query_relevant']")
    if not (second['every_query_relevant']):
        raise ValueError("Mathematical check failed: second['every_query_relevant']")
    if not (all((evaluate(small, a) == (a[0] and a[1]) for a in product([False, True], repeat=4)))):
        raise ValueError('Mathematical check failed: all((evaluate(small, a) == (a[0] and a[1]) for a in product([False, True], repeat=4)))')
    # These strict integer comparisons imply the logarithmic inequalities
    # by monotonicity of log, separately formalized in the Lean sources.
    if not (3 ** 3 < 2 ** 5):
        raise ValueError('Mathematical check failed: 3 ** 3 < 2 ** 5')
    if not (Fraction(3, 4) * Fraction(5, 3) == Fraction(5, 4)):
        raise ValueError('Mathematical check failed: Fraction(3, 4) * Fraction(5, 3) == Fraction(5, 4)')
    if not (3 ** 5 < 2 ** 8):
        raise ValueError('Mathematical check failed: 3 ** 5 < 2 ** 8')
    if not (Fraction(3007, 4096) * Fraction(8, 5) < Fraction(4863, 4096)):
        raise ValueError('Mathematical check failed: Fraction(3007, 4096) * Fraction(8, 5) < Fraction(4863, 4096)')
    print(json.dumps({"status": "all exact checks passed", "witnesses": [first, second]}, indent=2))


if __name__ == "__main__":
    main()
