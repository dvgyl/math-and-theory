"""Check the atom construction by exact product-sampling sums.

For each selected response, group one draw into lower, equal, and higher
reward. Enumerate every ordered tuple of those three groups. Their masses
are exact integers over one common denominator. This checks the sampling
law without assuming the CDF-power formula.
"""

if not __debug__:
    raise RuntimeError("Run this checker without Python optimization so that all mathematical checks execute.")

from fractions import Fraction as F
from itertools import product
from math import fsum, log
import json
import platform


def check(n, delta, full=False):
    a = min(delta, F(1, 8 * (n + 1)))
    threshold = a**n / (48 * (n + 1))
    bound = (1 - a) / threshold
    m = bound.numerator // bound.denominator + 1
    h = (1 - a) / m
    denom = a.denominator * h.denominator
    low_atom = int(a * denom)
    high_atom = int(h * denom)
    assert F(low_atom + m * high_atom, denom) == 1
    assert 0 < h <= threshold and max(a, h) <= delta
    samples = list(range(m + 1)) if full else sorted(set(
        list(range(12)) + list(range(m - 11, m + 1)) + [m//4, m//2, 3*m//4]
    ))
    # Every tuple is considered. Tuples with a higher reward or no equality
    # contribute zero to the event that this response is the maximum.
    patterns = list(product(range(3), repeat=n))
    selected_patterns = [p for p in patterns if max(p) == 1]
    total_q = 0
    win_numer = 0
    div_terms = []
    for i in samples:
        atom = low_atom if i == 0 else high_atom
        below = 0 if i == 0 else low_atom + (i - 1) * high_atom
        above = denom - below - atom
        group_masses = (below, atom, above)
        qnum = 0
        for pattern in selected_patterns:
            term = 1
            for group in pattern:
                term *= group_masses[group]
            qnum += term
        assert qnum == (below + atom)**n - below**n
        assert qnum > 0
        if full:
            total_q += qnum
            win_numer += qnum * (2 * below + atom)
            div_terms.append(qnum / denom**n * log(qnum / (denom**(n-1) * atom)))
    out = dict(n=n, delta=str(delta), a=str(a), m=m, h=str(h),
               atom_cap_pass=True, group_tuples_per_response=len(patterns),
               responses_checked=len(samples), product_sampling_pass=True,
               full_distribution_enumerated=full)
    if full:
        assert total_q == denom**n
        W = F(win_numer, 2 * denom**(n+1))
        assert F(1, 2) <= W < 1
        D = fsum(div_terms)
        curve = log(float(W / (1 - W))) + 1 / float(W) - 2
        assert curve > D
        out.update(selected_sum_exact=True, win_rate_exact=str(W),
                   divergence_numeric=D, gap_numeric=curve-D,
                   numeric_values_are_diagnostics=True)
    return out

results = [check(2, F(1, 2), full=True), check(2, F(1, 100), full=True),
           check(3, F(1, 2)), check(4, F(1, 10)), check(5, F(1, 100))]
print(json.dumps({
    "python": platform.python_version(),
    "status": "PASS",
    "checks": results,
    "limitation": "Exact grouped sampling checks cover the listed finite cases. Numerical KL values are diagnostics. The universal theorem is proved in Lean."
}, indent=2))
