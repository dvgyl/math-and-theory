#!/usr/bin/env python3
"""Independent checks for conditional_bound.txt. Requires numpy/scipy/sympy."""
from pathlib import Path
import json
import numpy as np
from numpy.linalg import norm, eigvalsh
import sympy as sp
from extension_checks import SIGMA, I2, bloch, canonical_density, lens_maximum


def bound_squared(r):
    return 1+(1+3*r)**2/(3+6*r-r*r)


def conditional(rho,u):
    L=np.kron(u.conj().reshape(1,2),I2)
    B=L@rho@L.conj().T
    return B/np.trace(B).real


def local_length(sigma):
    return norm(np.array([np.trace(sigma@s).real for s in SIGMA]))


def hidden_squared(rho):
    a,c,S,W,tau,H,g=canonical_density(rho)
    return lens_maximum(tau,H,g,a,(1-norm(a))/4)['value']


def exact_scalar_checks():
    r,t=sp.symbols('r t', real=True)
    alpha=(1+r)/2;beta=(1-r)/2
    D=3+6*r-r*r;N=1+3*r
    upper=8*t*alpha*(1-t)+2*t*t*(alpha*alpha+beta*beta)+2*(1-t)**2-4*t*beta*(1-t)-(2*t-1)**2
    assert sp.expand(upper-(1+2*N*t-D*t*t))==0
    assert sp.factor(1+N*N/D-upper-D*(t-N/D)**2)==0
    derivative=sp.diff(1+N*N/D,r)
    assert sp.factor(derivative-4*(1+3*r)*(3+5*r)/D**2)==0
    tau=2*alpha+alpha*alpha
    d=tau-beta*beta
    exact_value=tau+(alpha*beta)**2/(d-alpha*alpha)
    assert sp.factor(exact_value-(1+N*N/D))==0
    assert sp.factor(-alpha*beta/(d-alpha*alpha)+(1-r*r)/D)==0
    return {'scalar_quadratic_identity':True,'completed_square_identity':True,
        'strict_monotonicity_derivative_identity':True,
        'independent_canonical_value_identity':True,'canonical_optimizer_identity':True}


def main():
    rng=np.random.default_rng(2026110304)
    max_block_error=0.;max_invariance_error=0.;max_bound_excess=0.;projections=0
    for rank in [1,2,3,4]:
        for _ in range(12):
            Z=rng.normal(size=(4,rank))+1j*rng.normal(size=(4,rank))
            rho=Z@Z.conj().T;rho/=np.trace(rho)
            A=rho[:2,:2];B=rho[2:,2:];C=rho[:2,2:];t=np.trace(A).real
            value=np.sum(bloch(rho)[2]**2)
            block=(8*np.trace(C@C.conj().T)-4*abs(np.trace(C))**2+
                2*np.trace(A@A)+2*np.trace(B@B)-4*np.trace(A@B)-(2*t-1)**2).real
            max_block_error=max(max_block_error,abs(value-block))
            assert abs(value-block)<2e-12
            hidden=hidden_squared(rho)
            K=rng.normal(size=(2,2))+1j*rng.normal(size=(2,2))
            K/=norm(K,2)
            op=np.kron(K,I2);filtered=op@rho@op.conj().T;filtered/=np.trace(filtered)
            for _ in range(8):
                u=rng.normal(size=2)+1j*rng.normal(size=2);u/=norm(u)
                sigma=conditional(rho,u);r=local_length(sigma)
                assert r<=1+2e-12
                excess=hidden-bound_squared(r)
                assert excess<2e-10
                max_bound_excess=max(max_bound_excess,excess)
                v=np.linalg.solve(K.conj().T,u);v/=norm(v)
                err=norm(sigma-conditional(filtered,v))
                max_invariance_error=max(max_invariance_error,err)
                assert err<2e-10
                projections+=1
    sharp=[];max_sharp_error=0.;max_collapse_error=0.
    for r in [0.,.1,.25,.5,.75,.9,1.]:
        alpha=(1+r)/2;beta=(1-r)/2;t=(1+3*r)/(3+6*r-r*r)
        rho=np.diag([t*alpha,t*beta,0.,1-t]).astype(complex)
        rho[0,3]=rho[3,0]=np.sqrt(t*alpha*(1-t))
        assert min(eigvalsh(rho))>-2e-12
        direct=np.sum(bloch(rho)[2]**2);hidden=hidden_squared(rho)
        error=max(abs(direct-bound_squared(r)),abs(hidden-bound_squared(r)))
        max_sharp_error=max(max_sharp_error,error)
        assert error<2e-12
        collapse=[]
        for eps in [.1,.001,.00001]:
            state=np.diag([(1-eps)*alpha,(1-eps)*beta,0.,eps]).astype(complex)
            state[0,3]=state[3,0]=np.sqrt(eps*(1-eps)*alpha)
            hv=hidden_squared(state)
            max_collapse_error=max(max_collapse_error,abs(hv-bound_squared(r)))
            assert abs(hv-bound_squared(r))<2e-10
            limit=np.diag([alpha,beta,0.,0.])
            collapse.append({'epsilon':eps,'hidden_F3_squared':hv,
                'Frobenius_distance_to_singular_product':norm(state-limit)})
        sharp.append({'conditional_Bloch_length':r,'bound_squared':bound_squared(r),
            'sharp_t':t,'direct_squared_F3':direct,'hidden_squared_F3':hidden,
            'collapsing_sequence':collapse})
    result={'seed':2026110304,'random_physical_states':48,'density_ranks':[1,2,3,4],
        'conditional_projections':projections,'max_block_identity_error':max_block_error,
        'max_conditional_filter_invariance_error':max_invariance_error,
        'max_hidden_value_excess_over_bound':max_bound_excess,
        'max_sharp_family_error':max_sharp_error,
        'max_collapse_sequence_error':max_collapse_error,
        'exact_symbolic_checks':exact_scalar_checks(),'sharp_examples':sharp,
        'all_passed':True,'scope':'Exact scalar algebra plus floating-point physical checks; not a Lean quantum proof.'}
    Path(__file__).with_name('conditional_results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='sharp_examples'},indent=2))


if __name__=='__main__':
    main()
