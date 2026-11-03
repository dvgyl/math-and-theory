#!/usr/bin/env python3
"""Exact-form one-sided F3 criterion, with an independent optimization check.

This computes the theorem's criterion, not a general all-measurement steering test.
The algebraic theorem is in the report. Numerical eigenvalue tests are not exact
certificates near equality; rational inputs can use the report's adjugate tests.
"""
from fractions import Fraction as R
from pathlib import Path
import json
import numpy as np
from scipy.optimize import minimize
from reproduce import I, P, canonical, obs, sqrt_psd

def criterion(c,S):
    tau=float(np.sum(S*S)); k=S.T@c
    K=(tau-c@c)*np.eye(3)-S.T@S
    ev=np.linalg.eigvalsh(K)
    if ev.min()<=1e-12:
        return dict(violation=False,K=K,k=k,tau=tau,eigenvalues=ev)
    bs=np.linalg.solve(K,k); value=float(tau+k@bs)
    return dict(violation=bool(bs@bs<1-1e-10 and value>1+1e-10),K=K,k=k,tau=tau,
                eigenvalues=ev,b_star=bs,value=value,norm_squared=float(bs@bs))

def exact_example():
    c=R(3,10); sx=R(3,10); sy=R(-1,5); sz=R(3,5)
    tau=sx*sx+sy*sy+sz*sz
    K=[tau-c*c-s*s for s in [sx,sy,sz]]
    kz=c*sz; bs=kz/K[2]; V=tau+kz*bs
    assert all(x>0 for x in K) and bs>1 and V>1
    bound=tau+2*kz-K[2]
    assert bound==R(81,100)
    return dict(state_numerator=[[19,0,0,5],[0,7,1,0],[0,1,1,0],[5,0,0,13]],
                state_denominator=40,block_determinants=[222,6],
                tau=str(tau),K_diagonal=[str(x) for x in K],b_star_z=str(bs),
                unconstrained_value=str(V),actual_supremum=str(bound))

def main():
    rng=np.random.default_rng(391024)
    disagreements=[];max_formula_error=0.;max_value_error=0.;violations=0
    for i in range(240):
        rank=i%4+1
        X=rng.normal(size=(4,rank))+1j*rng.normal(size=(4,rank))
        rho=X@X.conj().T;rho/=np.trace(rho).real
        sigma=canonical(rho);c,_,S=obs(sigma);a=criterion(c,S)
        tau,K,k=a['tau'],a['K'],a['k']
        f=lambda b: tau+2*k@b-b@K@b
        grad=lambda b:2*k-2*K@b
        starts=[np.zeros(3)]
        for j in range(5):
            p=rng.normal(size=3);starts.append(.9*p/np.linalg.norm(p))
        values=[]
        for start in starts:
            res=minimize(lambda b:-f(b),start,jac=lambda b:-grad(b),
                         constraints=[dict(type='ineq',fun=lambda b:1-b@b,jac=lambda b:-2*b)],
                         method='SLSQP',options={'ftol':1e-12,'maxiter':300})
            if res.success and res.x@res.x<1+1e-7: values.append(f(res.x))
        best=max(values)
        if a['violation']:
            violations+=1;max_value_error=max(max_value_error,abs(best-a['value']))
        if bool(best>1+1e-7)!=a['violation']:
            disagreements.append(dict(index=i,best=best,criterion=a['violation']))
        b=rng.normal(size=3);b*=.8/np.linalg.norm(b)
        F=sqrt_psd(I+np.einsum('k,kij->ij',b,P));B=np.kron(I,F)
        actual=B@sigma@B;_,_,T=obs(actual)
        max_formula_error=max(max_formula_error,abs(f(b)-np.sum(T*T)))
    assert not disagreements,disagreements
    assert max_value_error<1e-7
    result=dict(seed=391024,states=240,rank_counts=[60,60,60,60],multistart_runs=1440,
                violations=violations,criterion_disagreements=disagreements,
                max_filter_formula_error=max_formula_error,max_violating_optimum_error=max_value_error,
                exact_norm_condition_counterexample=exact_example(),
                status='PASS; numerical optimization is corroboration, not proof')
    out=Path(__file__).with_name('one_sided_results.json');out.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
