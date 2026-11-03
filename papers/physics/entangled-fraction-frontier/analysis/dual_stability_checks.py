#!/usr/bin/env python3
"""Focused checks for the new explicit dual gap and Schmidt-number witness."""
from pathlib import Path
import json
import numpy as np


def certificate(a,b,p):
    d=len(a)
    m=np.minimum(a,b)
    s=np.sqrt(p)
    S=np.dot(s,np.sqrt(m))
    h=S*s/np.sqrt(m)
    theta=np.where(a<b,1.,np.where(a>b,0.,.5))
    x=np.zeros(d*d,complex)
    z=np.zeros(d*d,complex)
    x[np.arange(d)*(d+1)]=s
    z[np.arange(d)*(d+1)]=np.sqrt(m)
    H=np.kron(np.diag(theta*h),np.eye(d))+np.kron(np.eye(d),np.diag((1-theta)*h))-np.outer(x,x.conj())
    L=m.sum()
    zeta=z/np.sqrt(L)
    P=np.outer(zeta,zeta.conj())
    for i in range(d):
        for j in range(d):
            if a[i]>b[i] and b[j]>a[j]:
                P[i*d+j,i*d+j]+=1
    Q=np.eye(d*d)-P
    gamma=.5*np.min(h)
    cm=(d-1)**(d-1)*np.prod(m)/L**d
    return H,P,Q,gamma,cm,x,zeta,S


def main():
    rng=np.random.default_rng(20261103)
    records=[]
    for d in [2,3,4]:
        for sample in range(12):
            Z=rng.normal(size=(d*d,d*d))+1j*rng.normal(size=(d*d,d*d))
            rho=Z@Z.conj().T
            rho/=np.trace(rho)
            diagonal=np.diag(rho).real.reshape(d,d)
            a,b=diagonal.sum(axis=1),diagonal.sum(axis=0)
            # Force an equal-population case to check the half coefficient.
            if sample==0:
                a=b=(a+b)/2
                rho=np.kron(np.diag(a),np.diag(b))
            p=rng.dirichlet(np.ones(d))
            H,P,Q,gamma,cm,x,zeta,S=certificate(a,b,p)
            deficit=S*S-np.vdot(x,rho@x).real
            gap_min=np.linalg.eigvalsh(H-gamma*Q).min()
            err=abs(np.trace(rho@H).real-deficit)
            assert gap_min>-1e-12
            assert err<1e-12
            assert np.linalg.norm(H@P)<1e-12
            leakage=np.trace(rho@Q).real
            assert gamma*leakage<=deficit+1e-12
            if leakage<1-1e-12:
                projected=P@rho@P/(1-leakage)
                distance=.5*np.linalg.svd(rho-projected,compute_uv=False).sum()
                assert distance<=np.sqrt(leakage)+1e-12
            # A mixture of rank-(d-1) pure coefficient matrices.
            omega=np.zeros_like(rho,dtype=complex)
            for k in range(3):
                U=rng.normal(size=(d,d-1))+1j*rng.normal(size=(d,d-1))
                V=rng.normal(size=(d-1,d))+1j*rng.normal(size=(d-1,d))
                C=U@V
                vec=C.ravel()/np.linalg.norm(C)
                omega+=np.outer(vec,vec.conj())/3
            q=np.vdot(zeta,omega@zeta).real
            leakage_sn=np.trace(omega@Q).real
            witness_slack=leakage_sn-cm*q**d
            assert witness_slack>=-1e-12
            records.append({'d':d,'sample':sample,'dual_identity_error':float(err),
                'operator_gap_min_eigenvalue':float(gap_min),
                'kernel_residual_norm':float(np.linalg.norm(H@P)),
                'SN_at_most_d_minus_one_witness_slack':float(witness_slack)})
    result={'samples':len(records),
        'max_dual_identity_error':max(x['dual_identity_error'] for x in records),
        'min_gap_eigenvalue':min(x['operator_gap_min_eigenvalue'] for x in records),
        'max_kernel_residual':max(x['kernel_residual_norm'] for x in records),
        'min_SN_witness_slack':min(x['SN_at_most_d_minus_one_witness_slack'] for x in records),
        'records':records}
    Path(__file__).with_name('dual_stability_check_results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='records'},indent=2))


if __name__=='__main__':
    main()
