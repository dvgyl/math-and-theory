#!/usr/bin/env python3
"""Exact rational certificates for the one-sided F3 theorem.

Run with no arguments to reproduce the supplied examples, or give a JSON file
with keys c (three rational strings) and S (a 3x3 array of rational strings).
The script first verifies positivity of the actual 4x4 canonical density
matrix using every principal minor. It never uses floating-point eigenvalues.
This is an exact calculation, not a formally verified Python implementation.
"""
from itertools import combinations
from pathlib import Path
import argparse
import json
import sympy as sp


def rational(x):
    if not isinstance(x, (str, int)):
        raise TypeError('Use integer or rational-string inputs, not floating-point values.')
    return sp.Rational(x)


def certificate(c_data, S_data):
    c = sp.Matrix([rational(x) for x in c_data])
    S = sp.Matrix([[rational(x) for x in row] for row in S_data])
    if c.shape != (3, 1) or S.shape != (3, 3):
        raise ValueError('Expected c in R^3 and S a 3x3 matrix.')
    P = [sp.Matrix([[0, 1], [1, 0]]),
         sp.Matrix([[0, -sp.I], [sp.I, 0]]), sp.diag(1, -1)]
    rho = sp.eye(4)
    for i in range(3):
        rho += c[i] * sp.kronecker_product(P[i], sp.eye(2))
        for j in range(3):
            rho += S[i, j] * sp.kronecker_product(P[i], P[j])
    rho /= 4
    assert rho == rho.conjugate().T and sp.trace(rho) == 1
    minors = []
    for size in range(1, 5):
        for ix in combinations(range(4), size):
            d = sp.simplify(rho.extract(ix, ix).det())
            minors.append(dict(indices=list(ix), determinant=str(d)))
            if d < 0:
                raise ValueError(f'Input is not a physical canonical state: minor {ix} = {d}')
    tau = sp.trace(S.T * S)
    k = S.T * c
    K = (tau - (c.T * c)[0]) * sp.eye(3) - S.T * S
    leading = [sp.simplify(K[:i, :i].det()) for i in range(1, 4)]
    positive = all(d > 0 for d in leading)
    result = dict(c=[str(x) for x in c], S=[[str(S[i,j]) for j in range(3)] for i in range(3)],
                  physical_psd=True, state_rank=rho.rank(), principal_minors=minors,
                  tau=str(tau), K=[[str(K[i,j]) for j in range(3)] for i in range(3)],
                  k=[str(x) for x in k], K_leading_minors=[str(d) for d in leading],
                  K_positive_definite=positive, violation_possible=False)
    if positive:
        b = K.inv() * k
        norm_sq = sp.simplify((b.T * b)[0])
        value = sp.simplify(tau + (k.T * b)[0])
        inside = norm_sq < 1
        above = value > 1
        result.update(b_star=[str(x) for x in b], b_star_norm_squared=str(norm_sq),
                      vertex_inside_ball=bool(inside), unconstrained_value=str(value),
                      vertex_value_above_one=bool(above), violation_possible=bool(inside and above))
        if inside:
            result['attained_orbit_maximum_squared'] = str(value)
        # Independent Q-only/adjugate evaluation of the same two strict tests.
        Q = S * S.T
        L = (tau - (c.T * c)[0]) * sp.eye(3) - Q
        ell, R = L.det(), L.adjugate()
        ball_gap = sp.simplify(ell**2 - (c.T * Q * R * R * c)[0])
        value_gap = sp.simplify((tau - 1)*ell + (c.T * Q * R * c)[0])
        assert (ball_gap > 0) == inside and (value_gap > 0) == above
        result['adjugate_checks'] = dict(det_L=str(ell),
            ball_polynomial_gap=str(ball_gap), value_polynomial_gap=str(value_gap))
    return result


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('input', type=Path, nargs='?')
    args = p.parse_args()
    if args.input:
        data = json.loads(args.input.read_text())
        print(json.dumps(certificate(data['c'], data['S']), indent=2))
        return
    examples = {
        'bell': ([0,0,0], [[1,0,0],[0,-1,0],[0,0,1]]),
        'maximally_mixed': ([0,0,0], [[0,0,0],[0,0,0],[0,0,0]]),
        'werner_nonviolating': ([0,0,0], [['1/2',0,0],[0,'-1/2',0],[0,0,'1/2']]),
        'hidden_violation_rank_two': ([0,0,'16/25'], [['3/5',0,0],[0,'-3/5',0],[0,0,'9/25']]),
        'radius_condition_counterexample': ([0,0,'3/10'], [['3/10',0,0],[0,'-1/5',0],[0,0,'3/5']]),
        'pure_A_canonical_endpoint': ([0,0,1], [[0,0,0],[0,0,0],[0,0,0]]),
    }
    results = {name: certificate(*args) for name,args in examples.items()}
    assert results['bell']['attained_orbit_maximum_squared'] == '3'
    assert not results['maximally_mixed']['violation_possible']
    assert results['werner_nonviolating']['attained_orbit_maximum_squared'] == '3/4'
    h = results['hidden_violation_rank_two']
    assert h['tau'] == '531/625' and h['b_star'] == ['0','0','72/97']
    assert h['attained_orbit_maximum_squared'] == '99/97' and h['state_rank'] == 2
    assert not results['radius_condition_counterexample']['violation_possible']
    assert not results['pure_A_canonical_endpoint']['violation_possible']
    out = Path(__file__).with_name('exact_filter_certificates.json')
    out.write_text(json.dumps(results, indent=2) + '\n')
    print(json.dumps({name: {k:r[k] for k in ['state_rank','tau','K_positive_definite','violation_possible']}
                      for name,r in results.items()}, indent=2))


if __name__ == '__main__':
    main()
