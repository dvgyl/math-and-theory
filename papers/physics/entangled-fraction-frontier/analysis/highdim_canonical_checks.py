#!/usr/bin/env python3
"""Focused independent factor/sharpness check for the canonical-spectrum bound.

40 cases, d=3,4; includes zero-alpha and zero-residual cases. It checks the
actual Bell expectation, both marginals, whitening, positivity and the
classical-affinity stability consequence. It does not numerically optimize
general-dimensional FEF; the exact upper-bound proof identifies Bell
attainment as FEF attainment.
"""
import json
from pathlib import Path
import numpy as np


def marginals(rho,d):
    r = rho.reshape(d,d,d,d)
    return np.trace(r,axis1=1,axis2=3),np.trace(r,axis1=0,axis2=2)


def main():
    rng=np.random.default_rng(2026110302)
    result={"seed":2026110302,"cases":0,"dimensions":[3,4],
            "max_trace_error":0.,"max_marginal_error":0.,
            "max_whitening_error":0.,"max_attainment_error":0.,
            "max_negative_eigenvalue":0.,"max_stability_violation":0.,
            "alpha_rank_deficient_cases":0,"zero_residual_cases":0}
    for d in [3,4]:
        for case in range(20):
            alpha=np.sort(rng.dirichlet(np.ones(d)))[::-1]
            if case==0:
                alpha=np.ones(d)/d
                result["zero_residual_cases"]+=1
            if case==1:
                alpha=np.zeros(d);alpha[0]=1
                result["alpha_rank_deficient_cases"]+=1
            beta=np.sort(rng.dirichlet(np.ones(d)))[::-1]
            m=np.minimum(alpha,1/d)
            delta=1-m.sum()
            v=np.zeros(d*d)
            v[np.arange(d)*(d+1)]=np.sqrt(m)
            sigma=np.outer(v,v)
            if delta>1e-14:
                sigma+=np.diag(np.outer(alpha-m,np.ones(d)/d-m).reshape(-1)/delta)
            K=np.diag(np.sqrt(d*beta))
            KK=np.kron(np.eye(d),K)
            rho=KK@sigma@KK.T
            A,B=marginals(sigma,d)
            _,rhoB=marginals(rho,d)
            W=np.kron(np.eye(d),np.diag(1/np.sqrt(d*beta)))
            recovered=W@rho@W.T
            phi=np.zeros(d*d);phi[np.arange(d)*(d+1)]=1/np.sqrt(d)
            overlap=float(phi@rho@phi)
            frontier=float(np.sqrt(beta*m).sum()**2)
            L=float(m.sum());nu=m/L
            eps=L-overlap
            stability=float(np.abs(beta-nu).sum()-2*np.sqrt(max(0,eps/L)))
            result["cases"]+=1
            result["max_trace_error"]=max(result["max_trace_error"],abs(np.trace(rho)-1),abs(np.trace(sigma)-1))
            result["max_marginal_error"]=max(result["max_marginal_error"],
                float(np.max(abs(A-np.diag(alpha)))),float(np.max(abs(B-np.eye(d)/d))),
                float(np.max(abs(rhoB-np.diag(beta)))))
            result["max_whitening_error"]=max(result["max_whitening_error"],float(np.max(abs(recovered-sigma))))
            result["max_attainment_error"]=max(result["max_attainment_error"],abs(overlap-frontier))
            result["max_negative_eigenvalue"]=max(result["max_negative_eigenvalue"],-float(np.linalg.eigvalsh(rho).min()))
            result["max_stability_violation"]=max(result["max_stability_violation"],stability)
    for key,val in result.items():
        if key.startswith("max_"):
            assert val < 1e-12,(key,val)
    text=json.dumps(result,indent=2)
    Path(__file__).with_name("highdim_canonical_check_results.json").write_text(text+"\n")
    print(text)

if __name__=="__main__":
    main()
