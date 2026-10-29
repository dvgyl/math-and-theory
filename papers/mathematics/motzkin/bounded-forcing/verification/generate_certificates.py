#!/usr/bin/env python3
"""Regenerate certificates deliberately; the verifier never calls this script."""
from __future__ import annotations
import json
from fractions import Fraction as F
from pathlib import Path
from exact_poly import Poly

P_COEFFS = [4660409556032,24132003073520,56628081108524,
    79753800966621,75163688028504,49975719381810,24049942325892,
    8443039471929,2146478817312,385445807712,46409331456,3364180992,111034368]

def sequences(last: int):
    M = [1, 1]
    for n in range(1, last):
        u = (2*n+3)*M[n] + 3*n*M[n-1]
        if u % (n+3):
            raise ArithmeticError('Nonintegral Motzkin recurrence')
        M.append(u // (n+3))
    T = [1]
    for n in range(1, len(M)):
        T.append(M[n] - T[-1])
    return M, T

_, T = sequences(20)
x = Poly.variable(1, 0)
A = lambda n: T[n] + (x-1)*(-1)**n
family = {str(n): (A(n)*A(n+2)**3 - A(n+1)**3*A(n+3)).coefficients()
          for n in range(2, 12)}
P = Poly.from_coefficients(P_COEFFS)
quantitative = P - 800*65536*(x+3)**8*(x+4)**3*(x+5)
shifted = quantitative.evaluate([x+12]).coefficients()

# Rational isolating intervals. They will be checked by exact sign evaluation,
# not treated as floating-point estimates of the roots.
ratio_brackets = {"4":[201778,201779], "5":[231031,231032],
                  "6":[142954,142955], "7":[272862,272863], "9":[530293,530294]}
root_brackets = {"2":[171572,171573], "3":[407203,407204],
                 "4":[57244,57245], "5":[530571,530572]}

report = {
    'schema_version': 1,
    'coefficient_order': 'increasing degree',
    'arithmetic': 'integers and rational numbers only',
    'forcing_bound': 2,
    'uniform_start_index': 12,
    'quantitative_constant': 800,
    'P': P_COEFFS,
    'envelope_lower_numerator': [-1790,1599,1687,304],
    'envelope_upper_numerator': [-1331,-509,112],
    'quantitative_shift_at_12': shifted,
    'family_ratio_polynomials': family,
    'isolating_denominator': 1000000,
    'ratio_root_brackets': ratio_brackets,
    'root_gap_root_brackets': root_brackets,
    'ratio_root_order': [6,4,5,7,9],
    'root_gap_root_order': [4,2,3,5],
    'original_sharp_ratio_tail': 10,
    'original_sharp_root_tail': 5,
    'family_uniform_sharp_ratio_tail': 10,
    'family_uniform_sharp_root_tail': 5,
    'T_0_through_15': T[:16],
}
path = Path(__file__).resolve().parents[1] / 'proof' / 'certificates.json'
path.write_text(json.dumps(report, indent=2) + '\n')
print(path)
