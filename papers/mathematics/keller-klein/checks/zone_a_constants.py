"""Exact rational checks for the candidate zone-A analytic proof.

These finite algebra checks do not certify the analytic lemmas or any conjecture.
"""
from fractions import Fraction as Q

a = Q(7, 100)
high = (
    -Q(449, 9600) * Q(39, 100)
    + Q(5, 36) * a
    + Q(2, 5) * (Q(1371, 1280) + Q(1, 27)) * a**2
    + (128 + Q(1, 2160)) * a**5
)
low = (
    -Q(1, 15)
    + Q(2, 5) * (Q(1, 6) + Q(5, 54)) * a
    + Q(7, 108) * a**2
    + Q(2, 5) * (Q(113, 3840) + Q(1, 81)) * a**3
    + (128 + Q(1, 2160)) * a**6
)
assert high <= -Q(1, 200), (high, float(high))
assert low <= -Q(1, 20), (low, float(low))
print('high-theta gap / a^3 <=', high, '=', float(high))
print('low-theta gap / a^2 <=', low, '=', float(low))
