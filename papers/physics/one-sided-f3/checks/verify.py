"""Deterministic verification of formulas, certificates, and explicit cases.

Run: python verify.py
Dependencies: numpy, scipy.  Checks are numerical, except separately supplied
verify_galois_certificate.py, which uses exact rational/finite-field arithmetic.
"""
import json
from pathlib import Path
import numpy as np
from numpy.linalg import norm, eigvalsh
from f3_exact import (PAULI, I2, bloch, density, positive_sqrt, canonical,
                      one_sided, apply_filter, original_fraction, quadratic_spectral)


def random_rho(rng, rank):
    Z = rng.normal(size=(4, rank)) + 1j * rng.normal(size=(4, rank))
    R = Z @ Z.conj().T
    return R / np.trace(R)


def main():
    rng = np.random.default_rng(20261103)
    errors = {k: 0. for k in ['original_fraction', 'canonical', 'shape',
                              'recovered_filter', 'certificate', 'gap',
                              'shape_spectrum']}
    counts = {}
    nstates = 0
    for rank in [1, 2, 3, 4]:
        for _ in range(100):
            rho = random_rho(rng, rank)
            a, b, T = bloch(rho)
            nstates += 1
            for side in ['A', 'B']:
                aa, bb, TT = (a, b, T) if side == 'A' else (b, a, T.T)
                answer = one_sided(a, b, T, side)
                sol = answer['solution']
                counts[sol.branch] = counts.get(sol.branch, 0) + 1
                errors['certificate'] = max(errors['certificate'], sol.residual)
                filtered, prob = apply_filter(rho, answer['filter'], side)
                actual = float(norm(bloch(filtered)[2], 'fro')**2)
                errors['recovered_filter'] = max(errors['recovered_filter'],
                                                 abs(actual - answer['F3_squared']))
                c, S, Q = canonical(aa, bb, TT)
                errors['shape'] = max(errors['shape'], norm(Q - S.T @ S))
                ev = np.linalg.eigvals(answer['shape_spectral_matrix'])
                real = ev.real[np.abs(ev.imag) < 1e-7]
                if len(real):
                    errors['shape_spectrum'] = max(errors['shape_spectrum'],
                        abs(max(0, max(real)) - sol.multiplier))
                D = sol.multiplier * np.eye(3) - sol.H
                for __ in range(5):
                    x = rng.normal(size=3)
                    x *= rng.uniform()**(1/3) / norm(x)
                    E = I2 + np.einsum('i,ijk->jk', x, PAULI)
                    rr, _ = apply_filter(rho, positive_sqrt(E), side)
                    errors['original_fraction'] = max(errors['original_fraction'],
                        abs(norm(bloch(rr)[2], 'fro')**2 - original_fraction(aa, bb, TT, x)))
                    rc = density(np.zeros(3), c, S)
                    rr, _ = apply_filter(rc, positive_sqrt(E), 'A')
                    q = np.trace(Q) + 2 * sol.g @ x + x @ sol.H @ x
                    errors['canonical'] = max(errors['canonical'],
                        abs(norm(bloch(rr)[2], 'fro')**2 - q))
                    gap = sol.multiplier * (1 - x @ x) + (x-sol.x0) @ D @ (x-sol.x0)
                    errors['gap'] = max(errors['gap'], abs(sol.value - q - gap))
                    assert q <= sol.value + 1e-8
                assert 0 < prob <= 1 + 1e-9
                assert answer['F3_squared'] <= 3 + 1e-8
                if sol.value > 1 + 1e-8:
                    assert sol.multiplier == 0
                    assert min(eigvalsh(-sol.H)) > 0
                    assert norm(sol.x0) < 1
    cases = []
    # Werner states: max(3p^2,p^2)=3p^2, attained by identity except p=0.
    for p in [0., .2, .6, 1.]:
        r = one_sided(np.zeros(3), np.zeros(3), -p * np.eye(3))
        assert abs(r['F3_squared'] - 3*p*p) < 1e-10
        cases.append({'name':f'Werner p={p}', 'value_squared':r['F3_squared'], 'branch':r['branch']})
    # Product with filtered maximally mixed factor: supremum b^2, no GL maximum.
    r = one_sided(np.zeros(3), np.array([0.,0.,.6]), np.zeros((3,3)))
    assert abs(r['F3_squared'] - .36) < 1e-10 and not r['attained_invertibly']
    cases.append({'name':'full-rank product, no invertible maximizer', 'value_squared':r['F3_squared'], 'branch':r['branch']})
    # Pure marginal product.
    a, b = np.array([0.,0.,1.]), np.array([.2,.3,.1])
    r = one_sided(a,b,np.outer(a,b))
    assert abs(r['F3_squared'] - b@b) < 1e-10
    cases.append({'name':'pure marginal', 'value_squared':r['F3_squared'], 'branch':r['branch']})
    # Rank-one correlation: a continuum of invertible maximizers, singular D.
    T = np.diag([0.,0.,.5])
    r = one_sided(np.zeros(3),np.zeros(3),T)
    assert abs(r['F3_squared']-.25)<1e-10 and r['attained_invertibly']
    cases.append({'name':'singular D, flat maximum', 'value_squared':r['F3_squared'], 'branch':r['branch']})
    # Physical hard case with nonzero g: top eigenvector orthogonal to g.
    c=np.array([0.,0.,.3]); S=np.diag([.2,.1,.02])
    assert min(eigvalsh(density(np.zeros(3),c,S)))>0
    r=one_sided(np.zeros(3),c,S)
    assert r['branch']=='hard'
    cases.append({'name':'nontrivial physical hard case', 'value_squared':r['F3_squared'], 'branch':r['branch']})
    # Deliberate zero multiplier boundary case for generic TRS certificate.
    rr=quadratic_spectral(0.,-np.eye(3),np.array([1.,0.,0.]))
    assert abs(rr.value-1)<1e-10 and abs(norm(rr.x)-1)<1e-10
    cases.append({'name':'zero multiplier boundary, generic quadratic', 'value_squared':rr.value, 'branch':rr.branch})
    # Near-pure marginal is NOT the same as an exactly pure marginal: even
    # tiny entangled pure states have exact supremum sqrt(3), not about 1.
    for epsilon in [1e-13,1e-24]:
        psi=np.array([np.sqrt(1-epsilon),0,0,np.sqrt(epsilon)],complex)
        aa,bb,TT=bloch(np.outer(psi,psi.conj()))
        try:
            one_sided(aa,bb,TT)
        except ArithmeticError:
            cases.append({'name':f'near-pure entangled state precision guard eps={epsilon}',
                          'expected_exact_squared_value':3, 'rejected_float64_shortcut':True})
        else:
            raise AssertionError('Near-pure entangled state must not enter pure-product branch')
    for name,e in errors.items():
        assert e < 2e-7, (name,e)
    out={'seed':20261103,'random_states':nstates,'one_sided_instances':2*nstates,
         'ranks':[1,2,3,4],'max_absolute_errors':errors,'branches':counts,
         'explicit_cases':cases,'all_assertions_passed':True,
         'scope':'Floating-point falsification and reconstruction checks; not a proof.'}
    Path(__file__).with_name('verification_results.json').write_text(json.dumps(out,indent=2))
    print(json.dumps(out,indent=2))


if __name__=='__main__':
    main()
