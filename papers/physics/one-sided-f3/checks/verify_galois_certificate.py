#!/usr/bin/env python3
"""Exact arithmetic certificate for a physical F3 example with Galois group S6.

No third-party dependencies. Run with Python 3.9+:
    python verify_galois_certificate.py

The finite-field arithmetic is implemented below rather than delegated to a CAS.
All polynomial coefficients are stored in ascending order. The script verifies
the algebraic inputs to the Galois argument, whose short group-theoretic proof
is in the manuscript (Proposition on the physical obstruction to radicals). It also gives rational enclosures for the
largest real secular root and the optimum squared F3 value.

This is an exact computational certificate, not a Lean formalization.
"""

from fractions import Fraction as F
from functools import reduce
from math import gcd, isqrt, lcm
from pathlib import Path
import json


def trim(poly):
    poly = list(poly)
    while len(poly) > 1 and poly[-1] == 0:
        poly.pop()
    return poly


def add(a, b):
    return trim([
        (a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0)
        for i in range(max(len(a), len(b)))
    ])


def mul(a, b):
    out = [0] * (len(a) + len(b) - 1)
    for i, av in enumerate(a):
        for j, bv in enumerate(b):
            out[i + j] += av * bv
    return trim(out)


def product(polys):
    return reduce(mul, polys, [1])


def evaluate(poly, point):
    value = 0
    for coefficient in reversed(poly):
        value = value * point + coefficient
    return value


def mod(poly, p):
    return trim([v % p for v in poly])


def divmod_poly(a, b, p):
    a, b = mod(a, p), mod(b, p)
    assert b != [0]
    quotient = [0] * max(1, len(a) - len(b) + 1)
    inverse_leading = pow(b[-1], -1, p)
    while a != [0] and len(a) >= len(b):
        degree = len(a) - len(b)
        coefficient = a[-1] * inverse_leading % p
        quotient[degree] = coefficient
        for i, value in enumerate(b):
            a[i + degree] = (a[i + degree] - coefficient * value) % p
        a = trim(a)
    return trim(quotient), a


def remainder(a, b, p):
    return divmod_poly(a, b, p)[1]


def monic(a, p):
    a = mod(a, p)
    assert a != [0]
    inv = pow(a[-1], -1, p)
    return mod([inv * v for v in a], p)


def polynomial_gcd(a, b, p):
    a, b = mod(a, p), mod(b, p)
    while b != [0]:
        a, b = b, remainder(a, b, p)
    return monic(a, p)


def power_mod(a, exponent, modulus, p):
    answer = [1]
    a = remainder(a, modulus, p)
    while exponent:
        if exponent & 1:
            answer = remainder(mul(answer, a), modulus, p)
        a = remainder(mul(a, a), modulus, p)
        exponent >>= 1
    return answer


def is_prime(number):
    return number >= 2 and all(number % divisor for divisor in range(2, isqrt(number) + 1))


def prime_divisors(number):
    return [d for d in range(2, number + 1) if number % d == 0 and is_prime(d)]


def irreducibility_certificate(poly, p):
    """Rabin's exact criterion for irreducibility over the prime field."""
    assert is_prime(p)
    poly = monic(poly, p)
    degree = len(poly) - 1
    assert degree >= 1
    x = remainder([0, 1], poly, p)
    powers = [x]
    for _ in range(degree):
        powers.append(power_mod(powers[-1], p, poly, p))
    assert powers[degree] == x, "Frobenius degree test failed"
    checks = []
    for divisor in prime_divisors(degree):
        exponent = degree // divisor
        common = polynomial_gcd(poly, add(powers[exponent], [-v for v in x]), p)
        assert common == [1], "Proper subdegree factor detected"
        checks.append({
            "exponent": exponent,
            "x_to_p_power_mod_poly_low_to_high": powers[exponent],
            "gcd": common,
        })
    return {
        "prime": p,
        "degree": degree,
        "monic_polynomial_low_to_high": poly,
        "x_to_p_degree_mod_poly_low_to_high": powers[degree],
        "proper_subdegree_gcd_checks": checks,
    }


def linear_factors_and_remainder(poly, p):
    residual = monic(poly, p)
    factors = []
    for root in range(p):
        while len(residual) > 1 and evaluate(residual, root) % p == 0:
            factor = [(-root) % p, 1]
            residual, rest = divmod_poly(residual, factor, p)
            assert rest == [0]
            factors.append(factor)
    return factors, residual


def fraction_string(value):
    value = F(value)
    return str(value.numerator) if value.denominator == 1 else f"{value.numerator}/{value.denominator}"


def main():
    s = [F(1, 20), F(1, 15), F(1, 10)]
    c = [F(1, 5), F(1, 6), F(1, 7)]
    kappa = [v * v for v in s]
    g2 = [kappa[i] * c[i] ** 2 for i in range(3)]
    tau = sum(kappa)
    c2 = sum(v * v for v in c)
    assert tau == F(61, 3600)
    assert c2 == F(3889, 44100)
    assert sum(s) == F(13, 60)
    assert c2 < F(1, 9)
    assert F(1, 3) + sum(s) == F(11, 20) < 1
    assert tau < c2  # H = Q + (c2 - tau) I is strictly positive definite.

    factors = [[-value, F(1)] for value in kappa]
    squares = [mul(factor, factor) for factor in factors]
    polynomial = product(squares)
    for i in range(3):
        term = product([squares[j] for j in range(3) if j != i])
        polynomial = add(polynomial, [-g2[i] * coefficient for coefficient in term])
    common_denominator = reduce(lcm, [v.denominator for v in polynomial])
    integers = [int(common_denominator * v) for v in polynomial]
    common_factor = reduce(gcd, integers)
    integers = [v // common_factor for v in integers]
    expected = [
        -913, 695840, -188411500, 18599100000,
        65685000000, -107604000000000, 3175200000000000,
    ]
    assert integers == expected

    modular = {}
    for p in [17, 59, 487]:
        assert is_prime(p) and integers[-1] % p
        reduced = mod(integers, p)
        derivative = [i * reduced[i] % p for i in range(1, len(reduced))]
        assert polynomial_gcd(reduced, derivative, p) == [1]
        if p == 59:
            irreducible = irreducibility_certificate(reduced, p)
            irreducible_factors = [monic(reduced, p)]
            factor_certificates = [irreducible]
        else:
            linear, residual = linear_factors_and_remainder(reduced, p)
            expected_linear = 1 if p == 17 else 4
            assert len(linear) == expected_linear
            assert len(residual) - 1 == (5 if p == 17 else 2)
            certificate = irreducibility_certificate(residual, p)
            irreducible_factors = linear + [residual]
            factor_certificates = [certificate]
        leading = reduced[-1]
        reconstruction = mod([leading * v for v in product(irreducible_factors)], p)
        assert reconstruction == reduced
        modular[str(p)] = {
            "leading_coefficient": leading,
            "polynomial_low_to_high": reduced,
            "monic_irreducible_factors_low_to_high": irreducible_factors,
            "degrees": [len(factor) - 1 for factor in irreducible_factors],
            "nonlinear_factor_irreducibility_certificates": factor_certificates,
            "squarefree": True,
            "reconstruction_matches": True,
        }
    assert modular["59"]["degrees"] == [6]
    assert modular["17"]["degrees"] == [1, 5]
    assert modular["487"]["degrees"] == [1, 1, 1, 1, 2]

    # V = N(nu)/D(nu).  deg N = 4 < deg P = 6, and deg D = 3.
    denominator = product(factors)
    numerator = mul([c2, F(1)], denominator)
    for i in range(3):
        term = product([factors[j] for j in range(3) if j != i])
        numerator = add(numerator, [g2[i] * v for v in term])
    assert len(numerator) - 1 == 4 and numerator[-1] == 1
    assert len(denominator) - 1 == 3 and denominator[-1] == 1
    # None of the denominators vanish on the relevant root nu > max(kappa).
    lo, hi = F(2806139, 100000000), F(2806140, 100000000)
    assert lo > max(kappa)
    secular = lambda z: sum(g2[i] / (z - kappa[i]) ** 2 for i in range(3))
    assert secular(lo) > 1 and secular(hi) < 1
    optimum_lower = c2 + lo + sum(g2[i] / (hi - kappa[i]) for i in range(3))
    optimum_upper = c2 + hi + sum(g2[i] / (lo - kappa[i]) for i in range(3))

    results = {
        "status": "all exact checks passed",
        "canonical_state": {
            "a": ["0", "0", "0"],
            "diagonal_S": list(map(fraction_string, s)),
            "c": list(map(fraction_string, c)),
            "tau": fraction_string(tau),
            "c_squared": fraction_string(c2),
            "density_matrix_strict_lower_eigenvalue_bound": "9/80",
            "bound_is_strict": True,
            "positivity_reason": "||c|| < 1/3 and sum |Sii| = 13/60 imply ||I tensor c.sigma + sum Sii sigma_i tensor sigma_i|| < 11/20",
            "boundary_branch": True,
        },
        "secular_polynomial_integer_coefficients_high_to_low": integers[::-1],
        "modular_certificates": modular,
        "value_rational_function": {
            "numerator_low_to_high": list(map(fraction_string, numerator)),
            "denominator_low_to_high": list(map(fraction_string, denominator)),
            "numerator_degree": 4,
            "denominator_degree": 3,
            "nonrationality_argument": "If V were rational, nonzero N-V*D of degree 4 would annihilate the degree-6 algebraic number nu, contradiction.",
        },
        "rational_enclosures": {
            "nu_lower": fraction_string(lo),
            "nu_upper": fraction_string(hi),
            "V_lower": fraction_string(optimum_lower),
            "V_upper": fraction_string(optimum_upper),
            "V_lower_decimal_for_readability": float(optimum_lower),
            "V_upper_decimal_for_readability": float(optimum_upper),
        },
        "galois_argument": [
            "Irreducible reduction modulo 59 implies irreducibility over Q and transitivity of the characteristic-zero Galois group.",
            "Squarefree factor degrees (1,5) modulo 17 give a 5-cycle.",
            "A transitive subgroup of S6 containing a 5-cycle is primitive: the block containing the cycle's fixed point is invariant under the cycle and therefore has size 1 or 6.",
            "Squarefree factor degrees (1,1,1,1,2) modulo 487 give a transposition.",
            "A primitive permutation group containing a transposition is Sn: conjugate transpositions form the edge set of an invariant graph; its components are blocks, so the graph is connected and its edge transpositions generate Sn.",
            "Thus Gal(P/Q)=S6.  The point stabilizer S5 is maximal, so Q(nu) has no proper intermediate fields.",
            "V is a nonrational element of Q(nu), hence Q(V)=Q(nu).  The splitting field of its minimal polynomial has nonsolvable Galois group S6.",
            "Neither V nor sqrt(V) is expressible by radicals over Q.",
        ],
        "formalization_scope": "Exact arithmetic executable certificate plus a written group-theoretic argument; this script does not itself constitute a Lean proof.",
    }
    destination = Path(__file__).with_name("galois_results.json")
    destination.write_text(json.dumps(results, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({
        "status": results["status"],
        "polynomial_high_to_low": integers[::-1],
        "factor_patterns": {p: data["degrees"] for p, data in modular.items()},
        "nu_interval": [str(lo), str(hi)],
        "V_interval_approx": [float(optimum_lower), float(optimum_upper)],
        "result_file": str(destination),
    }, indent=2))


if __name__ == "__main__":
    main()
