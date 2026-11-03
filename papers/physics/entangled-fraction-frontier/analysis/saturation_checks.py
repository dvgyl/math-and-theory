#!/usr/bin/env python3
"""Focused independent checks of saturation-face extensions.

Exact arithmetic checks the d=4 nonuniqueness example. Floating-point tests
check only new residual/degeneracy/filter factors; these tests are evidence,
not substitutes for the accompanying exact proofs.
"""
from pathlib import Path
import json
import numpy as np
import sympy as sp


def marginals(rho, d):
    q = rho.reshape(d, d, d, d)
    return np.einsum('ijkj->ik', q), np.einsum('ijil->jl', q)


def diagonal_vector(m):
    d = len(m)
    z = np.zeros(d*d, complex)
    z[np.arange(d)*(d+1)] = np.sqrt(m)
    return z


def matrix_examples():
    a = np.array([.4, .3, .2, .1])
    b = np.array([.35, .33, .17, .15])
    m = np.minimum(a, b)
    u, v = a-m, b-m
    delta = u.sum()
    R0 = np.diag(np.outer(u,v).ravel()/delta).astype(complex)
    w = np.zeros(16, complex)
    w[0*4+3], w[2*4+1] = np.sqrt(.05), np.sqrt(.03)
    R1 = np.outer(w,w.conj())
    for s in [0, .2, .5, .8, 1]:
        yield f'fixed_full_marginals_d4_s{s}', a, b, (1-s)*R0+s*R1
    # Repeated cap value and rank-deficient marginal, with a quantum residual.
    a = np.array([.3, .25, .25, .2, 0.])
    b = np.array([.4, .2, .2, .1, .1])
    w = np.zeros(25, complex)
    w[1*5+0], w[2*5+4] = np.sqrt(.05), np.sqrt(.05)
    R = np.outer(w,w.conj())
    R[3*5+0,3*5+0] += .05
    R[3*5+4,3*5+4] += .05
    yield 'degenerate_and_zero_cap_d5', a, b, R
    # A mixed rank-deficient saturator becomes an exact rank-2 Bell state
    # when projecting away the entire residual, with nonzero success.
    a = np.array([.6,.4,0.])
    b = np.array([.6,.3,.1])
    R = np.zeros((9,9),complex)
    R[1*3+2,1*3+2]=.1
    yield 'mixed_exact_rank2_distillation_d3', a, b, R
    a=np.array([.97,.01,.01,.01])
    b=np.full(4,.25)
    R=np.zeros((16,16),complex)
    for j in range(1,4):
        R[j,j]=.24
    yield 'maximal_SN_below_teleportation_threshold_d4',a,b,R


def main():
    out = {'exact_d4': {}, 'state_checks': [], 'filter_checks': [],
           'G_concurrence_ensemble_checks': []}
    s = sp.symbols('s', real=True)
    dlt, L = sp.Rational(2,25), sp.Rational(23,25)
    r0sq = (sp.Rational(1,20)**2 + sp.Rational(3,100)**2)**2/dlt**2
    cross = (sp.Rational(1,20)**3 + sp.Rational(3,100)**3)/dlt
    purity = sp.expand(L**2 + (1-s)**2*r0sq + 2*s*(1-s)*cross + s**2*dlt**2)
    expected = (135713+30*s+705*s**2)/160000
    assert sp.simplify(purity-expected) == 0
    out['exact_d4'] = {
        'purity_polynomial': str(purity),
        'purity_product_residual': str(purity.subs(s,0)),
        'purity_entangled_pure_residual': str(purity.subs(s,1)),
        'purity_derivative_positive_on_0_1': True,
        'residual_product_trace_square': str(r0sq),
        'residual_cross_trace': str(cross),
    }
    rng = np.random.default_rng(14043951)
    for name, a, b, R in matrix_examples():
        d = len(a)
        m = np.minimum(a,b)
        z = diagonal_vector(m)
        rho = np.outer(z,z.conj()) + R
        A,B = marginals(rho,d)
        phi = diagonal_vector(np.ones(d)/d)
        bound = np.sqrt(m).sum()**2/d
        record = {
            'name':name,
            'min_eigenvalue':float(np.linalg.eigvalsh(rho).min()),
            'trace_error':float(abs(np.trace(rho)-1)),
            'marginal_error':float(max(np.max(abs(A-np.diag(a))),np.max(abs(B-np.diag(b))))),
            'target_bound_error':float(abs(np.vdot(phi,rho@phi).real-bound)),
            'rank':int(np.linalg.matrix_rank(rho,tol=1e-10)),
            'purity':float(np.trace(rho@rho).real),
            'schmidt_number_proved_by_support_theorem':int(np.count_nonzero(m>0)),
        }
        assert record['min_eigenvalue'] > -1e-13
        assert max(record[k] for k in ['trace_error','marginal_error','target_bound_error']) < 1e-13
        # The determinant identity is tested with generic complex residual coefficients.
        r = np.count_nonzero(m>0)
        Ia,Ib = np.flatnonzero(a>b),np.flatnonzero(b>a)
        N = np.zeros((d,d),complex)
        N[np.ix_(Ia,Ib)] = rng.normal(size=(len(Ia),len(Ib))) + 1j*rng.normal(size=(len(Ia),len(Ib)))
        coeff = .31+.27j
        C = coeff*np.diag(np.sqrt(m))+N
        det_error = abs(np.linalg.det(C[:r,:r])-coeff**r*np.sqrt(m[:r]).prod())
        record['support_minor_identity_error'] = float(det_error)
        assert det_error < 1e-13
        out['state_checks'].append(record)
        if r == d:
            vals,vecs=np.linalg.eigh(rho)
            active=vals>1e-12
            ensemble=vecs[:,active]*np.sqrt(vals[active])[None,:]
            nr=ensemble.shape[1]
            exact_G=d*np.prod(m)**(1/d)
            for sample in range(3):
                U,_=np.linalg.qr(rng.normal(size=(nr,nr))+1j*rng.normal(size=(nr,nr)))
                rotated=ensemble@U
                average_G=sum(d*abs(np.linalg.det(rotated[:,k].reshape(d,d)))**(2/d)
                              for k in range(nr))
                err=abs(average_G-exact_G)
                assert err < 1e-12
                out['G_concurrence_ensemble_checks'].append({
                    'state':name,'ensemble_sample':sample,'predicted_value':float(exact_G),
                    'average_value':float(average_G),'error':float(err)})
        mu = np.min(m[:r])
        Di = np.zeros(d)
        Di[:r]=m[:r]**(-.25)
        D = np.diag(Di)
        Dt = np.kron(D,D)
        Rt = Dt@R@Dt
        rR = np.trace(Rt).real
        phir=diagonal_vector(np.array([1/r]*r+[0.]*(d-r)))
        exponent = np.full(d,.5)
        exponent[Ia],exponent[Ib]=1.,0.
        for eps in [1.,.3,.1,.01]:
            Af = np.diag(mu**.25*Di*eps**exponent)
            Bf = np.diag(mu**.25*Di*eps**(1-exponent))
            K = np.kron(Af,Bf)
            actual = K@rho@K.conj().T
            expected = mu*eps**2*(r*np.outer(phir,phir.conj())+eps**2*Rt)
            P = mu*eps**2*(r+eps**2*rR)
            output = actual/np.trace(actual)
            F = r/(r+eps**2*rR)
            distance = .5*np.linalg.svd(output-np.outer(phir,phir.conj()),compute_uv=False).sum()
            check = {
                'state':name,'epsilon':eps,
                'filter_operator_norm':float(max(np.linalg.norm(Af,2),np.linalg.norm(Bf,2))),
                'unnormalized_identity_error':float(np.max(abs(actual-expected))),
                'success_probability':float(P),
                'success_probability_error':float(abs(np.trace(actual)-P)),
                'Bell_overlap':float(F),
                'Bell_overlap_error':float(abs(np.vdot(phir,output@phir).real-F)),
                'trace_distance_identity_error':float(abs(distance-(1-F))),
                'Bell_vector_top_eigenvector':bool(eps**2*np.linalg.eigvalsh(Rt).max() <= r+1e-12),
            }
            assert check['filter_operator_norm'] <= 1+1e-13
            assert max(check[k] for k in check if k.endswith('_error')) < 1e-13
            out['filter_checks'].append(check)
    dest=Path(__file__).with_name('saturation_check_results.json')
    dest.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))


if __name__=='__main__':
    main()
