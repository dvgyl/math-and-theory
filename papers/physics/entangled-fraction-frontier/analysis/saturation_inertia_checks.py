#!/usr/bin/env python3
"""Exact checks for the saturation normal form and partial-transpose theorem.

All matrix identities and signs below use exact SymPy rational/complex
arithmetic. Numerical marginal spectra are an additional counterexample
search, never the proof of an identity. No Lean claim is made for this file.
"""
from pathlib import Path
import json
import random

import numpy as np
import sympy as s


def pt(M, d):
    return s.Matrix(d*d, d*d, lambda a, b:
                    M[(a//d)*d+b%d, (b//d)*d+a%d])


def marginals(M, d):
    return (s.Matrix(d, d, lambda i, k: sum(M[i*d+j, k*d+j] for j in range(d))),
            s.Matrix(d, d, lambda j, l: sum(M[i*d+j, i*d+l] for i in range(d))))


def assert_zero(M):
    assert all(s.simplify(v) == 0 for v in M)


def embed(R, positions, d):
    out = s.zeros(d*d)
    for i, p in enumerate(positions):
        for j, q in enumerate(positions):
            out[p[0]*d+p[1], q[0]*d+q[1]] = R[i, j]
    return out


def random_residual(positions, delta, d, seed):
    rng = random.Random(seed)
    k = len(positions)
    H = s.Matrix(k, k, lambda i, j:
                 rng.randint(-2, 2)+s.I*rng.randint(-2, 2))
    Q = (H*H.H+s.eye(k)).applyfunc(s.expand)
    return embed(delta*Q/s.trace(Q), positions, d)


def uniform_quantum_residual(d, delta, eta):
    # Alice support {0,1}; Bob support {2,...,d-1}, in pairs.
    positions = [(i, j) for i in range(2) for j in range(2, d)]
    k = len(positions)
    Q = eta*s.eye(k)/k
    blocks = (d-2)//2
    for b in range(blocks):
        z = s.zeros(k, 1)
        z[positions.index((0, 2+2*b))] = 1
        z[positions.index((1, 3+2*b))] = s.I if b % 2 == 0 else -s.I
        Q += (1-eta)*(z*z.H)/(2*blocks)
    assert s.trace(Q) == 1
    return embed(delta*Q, positions, d)


def check_case(name, a, scale, IA, IB, R, filters=False):
    d = len(a)
    r = sum(v > 0 for v in a)
    m = [s.Rational(v*v, scale) for v in a]
    core = s.zeros(d*d)
    for i in range(d):
        for j in range(d):
            core[i*d+i, j*d+j] = s.Rational(a[i]*a[j], scale)
    rho = core+R
    assert s.simplify(s.trace(rho)-1) == 0
    assert_zero(rho-rho.H)
    A, B = marginals(rho, d)
    numerical = lambda M: np.array(M.evalf(), dtype=complex)
    alpha = np.linalg.eigvalsh(numerical(A))[::-1]
    beta = np.linalg.eigvalsh(numerical(B))[::-1]
    cap_error = float(np.max(np.abs(np.minimum(alpha, beta)-np.array(m, dtype=float))))
    assert cap_error < 2e-12
    bell = s.zeros(d*d, 1)
    for i in range(d):
        bell[i*d+i] = 1
    assert s.simplify((bell.H*rho*bell)[0]/d-s.Rational(sum(a)**2, scale*d)) == 0

    # Exact positive-prefix compression and shear to the pure-core partial transpose.
    indices = [i*d+j for i in range(r) for j in range(r)]
    P = pt(rho, d).extract(indices, indices)
    P0 = pt(core, d).extract(indices, indices)
    T = [(i, j) for i in IA for j in IB if i < r and j < r]
    t = [i*r+j for i, j in T]
    tf = [j*r+i for i, j in T]
    S = s.eye(r*r)
    if T:
        C = P.extract(t, t)
        D = s.diag(*[s.Rational(a[i]*a[j], scale) for i, j in T])
        lower = -D.inv()*C/2
        for i, row in enumerate(tf):
            for j, col in enumerate(t):
                S[row, col] = lower[i, j]
    assert_zero(S.H*P*S-P0)

    # An explicit, unnormalized Hadamard change on every pair diagonalizes P0.
    H = s.eye(r*r)
    expected = s.zeros(r*r)
    for i in range(r):
        expected[i*r+i, i*r+i] = m[i]
        for j in range(i+1, r):
            u, v = i*r+j, j*r+i
            H[u, u], H[u, v], H[v, u], H[v, v] = 1, 1, 1, -1
            expected[u, u] = s.Rational(2*a[i]*a[j], scale)
            expected[v, v] = -expected[u, u]
    assert_zero(H.H*P0*H-expected)
    positive = sum(1 for v in expected.diagonal() if v > 0)
    negative = sum(1 for v in expected.diagonal() if v < 0)
    assert (positive, negative) == (r*(r+1)//2, r*(r-1)//2)

    # Every retained positive pair has an exact Schmidt-rank-two NPT witness.
    PT = pt(rho, d)
    for i in range(r):
        for j in range(i+1, r):
            assert s.simplify(PT.extract([i*d+j, j*d+i], [i*d+j, j*d+i]).det()
                              + m[i]*m[j]) == 0

    # Exact triangular minor underlying the Schmidt-number theorem.
    C = s.Rational(2, 3)*s.diag(*a)
    for i in IA:
        for j in IB:
            C[i, j] += (i+1)+s.I*(j+1)
    assert s.simplify(C[:r, :r].det()-s.Rational(2, 3)**r*s.prod(a[:r])) == 0

    record = dict(name=name, d=d, positive_cap_rank=r, exact_congruence=True,
                  compressed_inertia=[positive, negative, 0],
                  exact_two_level_minor_count=r*(r-1)//2,
                  exact_schmidt_minor=True, numerical_cap_max_error=cap_error)
    if filters:
        eps = s.Rational(1, 4)
        amin = min(a[:r])
        mu = s.Rational(amin*amin, scale)
        fa, fb = [], []
        for i in range(d):
            if not a[i]:
                fa.append(s.S.Zero); fb.append(s.S.Zero)
                continue
            factor = s.sqrt(s.Rational(amin, a[i]))
            power = 1 if i in IA else 0 if i in IB else s.Rational(1, 2)
            fa.append(factor*eps**power)
            fb.append(factor*eps**(1-power))
        K = s.diag(*[fa[i]*fb[j] for i in range(d) for j in range(d)])
        out = K*rho*K
        E = s.diag(*[1/s.sqrt(a[i]*a[j]) if a[i]*a[j] else 0
                     for i in range(d) for j in range(d)])
        Rtilde = scale*E*R*E
        ur = s.zeros(d*d, 1)
        for i in range(r):
            ur[i*d+i] = 1
        assert_zero(out-mu*eps**2*(ur*ur.H+eps**2*Rtilde))
        rr = s.simplify(s.trace(Rtilde))
        probability = s.simplify(s.trace(out))
        assert s.simplify(probability-mu*eps**2*(r+eps**2*rr)) == 0
        fidelity = s.simplify((ur.H*out*ur)[0]/(r*probability))
        assert s.simplify(fidelity-r/(r+eps**2*rr)) == 0
        assert_zero(Rtilde*ur)
        record.update(exact_filter_identity=True, residual_whitened_trace=str(rr),
                      success_probability=str(probability), bell_overlap=str(fidelity))
    return record


def main():
    records = []
    for d in range(2, 6):
        a = list(range(d, 0, -1))
        scale = sum(v*v for v in a)+1
        IA, IB = list(range(0, d, 2)), list(range(1, d, 2))
        positions = [(i, j) for i in IA for j in IB]
        R = random_residual(positions, s.Rational(1, scale), d, 1700+d)
        records.append(check_case(f'full_complex_d{d}', a, scale, IA, IB, R, d == 3))
    for eta in [s.S.Zero, s.Rational(1, 5)]:
        d, a, scale = 6, [100, 100, 1, 1, 1, 1], 60000
        delta = 1-s.Rational(sum(v*v for v in a), scale)
        R = uniform_quantum_residual(d, delta, eta)
        records.append(check_case(f'full_degenerate_large_residual_eta{eta}',
                                  a, scale, [0, 1], [2, 3, 4, 5], R, True))
    for d, r in [(4, 2), (5, 3)]:
        a = list(range(r, 0, -1))+[0]*(d-r)
        scale = sum(v*v for v in a)+1
        IA, IB = [0]+list(range(r, d)), list(range(1, r))
        R = random_residual([(i, j) for i in IA for j in IB],
                            s.Rational(1, scale), d, 1900+d)
        records.append(check_case(f'zero_caps_d{d}_r{r}', a, scale, IA, IB, R, True))
    R = uniform_quantum_residual(6, s.Rational(2, 3), s.Rational(1, 5))
    records.append(check_case('zero_caps_quantum_residual_d6_r2',
                              [1, 1, 0, 0, 0, 0], 6, [0, 1], [2, 3, 4, 5], R, True))
    result = dict(all_passed=True, exact_case_count=len(records), cases=records,
                  scope='Exact algebraic checks supplement the analytic proof; numerical spectra are only counterexample searches.')
    output = Path(__file__).with_name('saturation_inertia_checks.json')
    output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
