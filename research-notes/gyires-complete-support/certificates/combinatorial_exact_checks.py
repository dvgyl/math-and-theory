#!/usr/bin/env python3
"""Exact rational checks for support, monotonicity, and convexity counterexamples.

This is an arithmetic checker, not a proof-assistant formalization. The analytic
derivations for capacity minimizers, derivatives, and Lorentzianity are in the Gyires manuscript.
"""

if not __debug__:
    raise RuntimeError("Certificate checks require assertions. Run Python without -O or PYTHONOPTIMIZE.")

from fractions import Fraction as F
from collections import defaultdict
from math import factorial, prod
import json


def cycle_product(n):
    p = {(0,)*n: 1}
    for i in range(n):
        q = defaultdict(int)
        for a, value in p.items():
            for j in (i, (i+1) % n):
                b = list(a)
                b[j] += 1
                q[tuple(b)] += value
        p = q
    return dict(p)


def main():
    # Same-support EGF domination fails at the four-cycle.
    p = cycle_product(4)
    center = p[(1,)*4]
    norm = sum(prod(factorial(k) for k in a)*v*v for a, v in p.items())
    egf_norm = sum((F(1, prod(factorial(k) for k in a)) for a in p), F(0))
    assert center == 2 and norm == 36 and egf_norm == F(15, 2)
    assert F(norm, center*center) == 9 > egf_norm

    # Monotonicity counter: dG/dlambda = -4/(81 sqrt(3)) < 0.
    assert F(8, 27)/F(4, 3) + F(12, 27) + F(6, 27)*F(4, 3) == F(26, 27)

    # Nonconvexity counter: the squared first-order displacement is 3/56.
    k_squared = F(3, 14)**2 * F(7, 6)
    assert k_squared == F(3, 56)
    right_derivative = F(2, 9)*(2*k_squared + F(13, 6))
    assert right_derivative == F(191, 378)
    f = lambda t: 3*t**3 - 3*t - 1
    assert f(F(9, 8)) == F(-53, 512) < 0
    assert f(F(8, 7)) == F(17, 343) > 0
    upper_norm = 2 + F(64, 49) + F(64, 81) + F(2048, 19683)
    assert upper_norm < F(359, 84)
    endpoint_upper = F(2, 9)*upper_norm
    assert endpoint_upper < F(4, 9) + right_derivative

    result = {
        'status': 'all exact rational assertions passed',
        'same_support_product_normalized_norm': str(F(norm, center*center)),
        'same_support_EGF_norm': str(egf_norm),
        'monotonicity_counter_G0': '26/27',
        'monotonicity_counter_right_derivative': '-4/(81*sqrt(3))',
        'convexity_counter_G0': '4/9',
        'convexity_counter_right_derivative': str(right_derivative),
        'convexity_counter_G1_upper_bound': str(endpoint_upper),
        'convexity_counter_chord_slope_upper_bound': str(endpoint_upper-F(4, 9)),
    }
    json.dump(result, open('combinatorial_exact_checks.json', 'w'), indent=2)
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
