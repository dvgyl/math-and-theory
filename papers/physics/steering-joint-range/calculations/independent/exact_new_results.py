"""Exact checks of the new results, written separately from the package's other checkers.

Usage: python3 -I calculations/independent/exact_new_results.py [--output result.json]

Every quantity is computed from an explicit 4x4 density matrix through Pauli
traces, in exact SymPy arithmetic (rationals and square roots). The checks are:

1. joint interval: the lower witness, the upper witness and their mixtures have
   the prescribed centre length c and Bob length r, and F3^2 runs from
   max(0, c(1+r)-1)^2 to H_c(r); the probability identity behind the lower bound;
2. volume: for the general radial matrix form, det S = 4t(|v|^2-|w|^2) and
   tau = t^2 + 8(|w|^2+|v|^2+2|z|^2); the explicit X states attain
   (t/2) min(tau-t^2, 1+2t+2t^2-c^2-tau) on a rational grid of (c, t, tau);
3. probability frontier: the critical centre 2/(1+p+sqrt((1-p)^2+2)) is the
   root of H_c((1-p)/p) = 1, and violation within the success budget happens
   exactly below it on a rational grid;
4. the rational activation example at c = 16/25.
It supports, but does not replace, the written and Lean proofs.
"""
import argparse
import itertools
import json

import sympy as sp

I2 = sp.eye(2)
PAULI = [sp.Matrix([[0, 1], [1, 0]]), sp.Matrix([[0, -sp.I], [sp.I, 0]]), sp.Matrix([[1, 0], [0, -1]])]


def kron(a, b):
    return sp.kronecker_product(a, b)


def bloch(rho):
    """Alice vector a, Bob vector b and correlation matrix T of a 4x4 matrix."""
    a = [sp.simplify(sp.re((rho * kron(P, I2)).trace())) for P in PAULI]
    b = [sp.simplify(sp.re((rho * kron(I2, P)).trace())) for P in PAULI]
    T = sp.Matrix(3, 3, lambda i, j: sp.simplify(sp.re((rho * kron(PAULI[i], PAULI[j])).trace())))
    return sp.Matrix(a), sp.Matrix(b), T


def is_psd(M):
    """Positive semidefiniteness via all principal minors, decided exactly by SymPy.

    The minors here are rationals or simple surds; a minor whose sign SymPy
    cannot decide symbolically is rejected rather than estimated.
    """
    n = M.shape[0]
    for k in range(1, n + 1):
        for idx in itertools.combinations(range(n), k):
            m = sp.radsimp(sp.simplify(M.extract(list(idx), list(idx)).det()))
            if m.is_nonnegative is not True:
                raise AssertionError(f"undecided or negative minor {m}")
    return True


def centre(rho):
    a, b, T = bloch(rho)
    r2 = sp.simplify((b.T * b)[0])
    vec = (a - T * b) / (1 - r2)
    return sp.sqrt(sp.simplify((vec.T * vec)[0])), sp.sqrt(r2), T


def fsq(T):
    return sp.simplify(sum(x**2 for x in T))


def H(c, r):
    return (1 - r**2) * (3 - 4 * c) + (c + (1 - c) * r) ** 2


def joint_witnesses(c, r):
    x = max(sp.Integer(0), c * (1 + r) - 1)
    a0 = c * (1 - r**2) + r * x
    low = sp.diag(1 + a0 + r + x, 1 + a0 - r - x, 1 - a0 + r - x, 1 - a0 - r + x) / 4
    s = sp.sqrt((1 - c) * (1 - r**2))
    up = sp.Matrix([[1 + r, 0, 0, s], [0, c * (1 - r), 0, 0], [0, 0, 0, 0],
                    [s, 0, 0, (1 - c) * (1 - r)]]) / 2
    return x, low, up


def check_joint():
    grid = [sp.Rational(k, 6) for k in range(7)]
    rgrid = [sp.Rational(k, 7) for k in range(7)]
    alpha = sp.symbols('alpha', real=True)
    count = 0
    for c in grid:
        for r in rgrid:
            x, low, up = joint_witnesses(c, r)
            for M in (low, up):
                assert M.trace() == 1 and is_psd(M), (c, r)
                cc, rr, T = centre(M)
                assert sp.simplify(cc - c) == 0 and sp.simplify(rr - r) == 0, (c, r)
            assert fsq(bloch(low)[2]) == x**2
            assert sp.simplify(fsq(bloch(up)[2]) - H(c, r)) == 0
            mix = (1 - alpha) * low + alpha * up
            cc, rr, T = centre(mix)
            assert sp.simplify(cc**2 - c**2) == 0 and sp.simplify(rr - r) == 0
            d, z = 1 - c, 1 - c + c * r
            formula = 2 * alpha**2 * d * (1 - r**2) + (x + alpha * (z - x)) ** 2
            assert sp.expand(fsq(T) - formula) == 0
            assert sp.simplify(z - x) >= 0
            count += 1
    # Identity behind the lower bound: P(--) * 4 = 1 - a.n - r + q with a.n = (1-r^2)c + r q.
    c, r, q = sp.symbols('c r q', real=True)
    lhs = 1 - ((1 - r**2) * c + r * q) - r + q
    assert sp.expand(lhs - (1 - r) * (q - (c * (1 + r) - 1))) == 0
    return {"grid_points": count, "lower_bound_identity": True}


def check_volume():
    c, t = sp.symbols('c t', nonnegative=True)
    zr, zi, wr, wi, vr, vi = sp.symbols('zr zi wr wi vr vi', real=True)
    z, w, v = zr + sp.I * zi, wr + sp.I * wi, vr + sp.I * vi
    a, b, e, d = (1 + c + t) / 4, (1 + c - t) / 4, (1 - c - t) / 4, (1 - c + t) / 4
    M = sp.Matrix([[a, 0, z, w], [0, b, v, -z],
                   [sp.conjugate(z), sp.conjugate(v), e, 0],
                   [sp.conjugate(w), -sp.conjugate(z), 0, d]])
    A, B, S = bloch(M)
    assert sp.simplify(A - sp.Matrix([0, 0, c])) == sp.zeros(3, 1)
    assert sp.simplify(B) == sp.zeros(3, 1)
    assert sp.simplify(S.T * sp.Matrix([0, 0, 1]) - sp.Matrix([0, 0, t])) == sp.zeros(3, 1)
    W, J, Z = wr**2 + wi**2, vr**2 + vi**2, zr**2 + zi**2
    assert sp.expand(S.det() - 4 * t * (J - W)) == 0
    assert sp.expand(fsq(S) - (t**2 + 8 * (W + J + 2 * Z))) == 0
    # Sharp witnesses on a rational grid of feasible triples.
    count = 0
    for cv in [sp.Rational(k, 5) for k in range(6)]:
        for tv in [sp.Rational(k, 10) for k in range(11)]:
            if tv > 1 - cv:
                continue
            lo, hi = tv**2, 1 - cv**2 + 2 * tv**2
            for j in range(5):
                tau = lo + (hi - lo) * sp.Rational(j, 4)
                U = ((1 + tv) ** 2 - cv**2) / 16
                V = ((1 - tv) ** 2 - cv**2) / 16
                s = (tau - tv**2) / 8
                Wv, Jv = (s, sp.Integer(0)) if s <= U else (U, s - U)
                sub = {c: cv, t: tv, zr: 0, zi: 0, wr: sp.sqrt(Wv), wi: 0, vr: sp.sqrt(Jv), vi: 0}
                Mv = M.subs(sub)
                assert Mv.trace() == 1 and is_psd(Mv)
                _, _, Sv = bloch(Mv)
                assert sp.simplify(fsq(Sv) - tau) == 0
                cap = tv / 2 * sp.Min(tau - tv**2, 1 + 2 * tv + 2 * tv**2 - cv**2 - tau)
                assert sp.simplify(abs(Sv.det()) - cap) == 0, (cv, tv, tau)
                assert Jv <= V
                count += 1
    return {"symbolic_identities": True, "attaining_witnesses": count}


def check_probability():
    p, c = sp.symbols('p c', positive=True)
    R = (1 - p) / p
    crit = 2 / (1 + p + sp.sqrt((1 - p) ** 2 + 2))
    # c_crit is the root in [0,1] of (1-2p)c^2 + (2+2p)c - 2 = 0, i.e. H_c(R) = 1.
    poly = sp.expand(p * (1 - H(c, R)) / (1 - R))
    assert sp.simplify(poly - ((1 - 2 * p) * c**2 + (2 + 2 * p) * c - 2)) == 0
    count = 0
    for pv in [sp.Rational(1, 2) + sp.Rational(k, 20) for k in range(11)]:
        cv_crit = crit.subs(p, pv)
        assert sp.simplify(((1 - 2 * pv) * cv_crit**2 + (2 + 2 * pv) * cv_crit - 2)) == 0
        Rv = (1 - pv) / pv
        for cv in [sp.Rational(k, 60) for k in range(61)]:
            D = 2 - 2 * cv - cv**2
            rstar = cv * (1 - cv) / D if cv <= sp.Rational(2, 3) else None
            rhat = Rv if rstar is None else min(Rv, rstar)
            best = H(cv, rhat)
            # brute-force check of the maximiser on a fine grid of radii
            for k in range(41):
                assert H(cv, Rv * sp.Rational(k, 40)) <= best
            violation = best > 1
            if pv == sp.Rational(1, 2):
                # R = 1 is the product boundary; strict violation needs r < 1.
                violation = rstar is not None and rstar < 1 and H(cv, rstar) > 1
            assert violation == bool(cv < cv_crit), (pv, cv)
            count += 1
    assert crit.subs(p, sp.Rational(1, 2)) == sp.Rational(2, 3)
    assert sp.simplify(crit.subs(p, 1) - (2 - sp.sqrt(2))) == 0
    return {"grid_points": count, "endpoints": ["2/3", "2-sqrt(2)"]}


def check_example():
    sigma = sp.Matrix([[25, 0, 0, 15], [0, 16, 0, 0], [0, 0, 0, 0], [15, 0, 0, 9]]) / 50
    assert is_psd(sigma) and sigma.trace() == 1
    a, b, T = bloch(sigma)
    assert b == sp.zeros(3, 1) and sp.sqrt((a.T * a)[0]) == sp.Rational(16, 25)
    assert fsq(T) == sp.Rational(531, 625)
    G = kron(I2, sp.diag(1, sp.Rational(5, 13)))
    out = G * sigma * G.H
    prob = out.trace()
    assert prob == sp.Rational(97, 169)
    rho = out / prob
    assert rho == sp.Matrix([[169, 0, 0, 39], [0, 16, 0, 0], [0, 0, 0, 0], [39, 0, 0, 9]]) / 194
    cc, rr, T2 = centre(rho)
    assert cc == sp.Rational(16, 25) and fsq(T2) == sp.Rational(99, 97)
    D = 2 - 2 * cc - cc**2
    assert 1 + (2 - 3 * cc) ** 2 / D == sp.Rational(99, 97)
    return {"success_probability": "97/169", "output_F3_squared": "99/97", "centre": "16/25"}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output")
    args = parser.parse_args()
    result = {
        "joint_interval": check_joint(),
        "volume": check_volume(),
        "probability_frontier": check_probability(),
        "activation_example": check_example(),
        "sympy": sp.__version__,
        "status": "PASS",
    }
    text = json.dumps(result, indent=2)
    if args.output:
        with open(args.output, "w") as handle:
            handle.write(text + "\n")
    print(text)


if __name__ == "__main__":
    main()
