"""Well-conditioned interval SDP with the constant-history kernel eliminated.

Search only; exact reconstruction and the independent checker are mandatory.
"""
import argparse,json,time
from pathlib import Path
import numpy as np
import cvxpy as cp
from scipy.linalg import null_space
from robust_interval_certificate import matrices


def solve(lo,hi,m,scale,supported_lower=False):
    n=2*(m+1);d=2*m
    J=np.tile(np.eye(2),(m+1,1));C=J[:d]
    U=null_space(C.T)
    B=np.zeros((n,d))
    for i in range(n):
        for j in range(d):
            B[i,j]=int(i%2==j%2 and j//2<i//2)
    data,*_=matrices(lo,m)
    lam=cp.Variable(len(data),nonneg=True)
    constraints=[np.array([r['F'] for r in data]).T@lam==0]
    lower_indices=[i for i,r in enumerate(data) if r['i']<m and r['j']<m]
    mu=cp.Variable(len(lower_indices),nonneg=True) if supported_lower else None
    if supported_lower:
        constraints.append(np.array([data[i]['F'] for i in lower_indices]).T@mu==0)
    Ps=[];Ts=[];Ls=[]
    for tau in [lo,hi]:
        data,S0,S1,D,diss,coerc=matrices(tau,m)
        Q=cp.reshape(np.column_stack([r['Q'].ravel() for r in data])@lam,(n,n),order='C')
        W=Q@J
        # R contains the cumulative pairs of rows of QJ.
        R=B.T@W
        # B^T computes suffix sums. Since total W=0, prefixes are minus suffixes.
        R=-R
        constraints += [J.T@W==0,C.T@R==R.T@C]
        H=cp.Variable((d-2,d-2),symmetric=True)
        P=(R@C.T+C@R.T)/m-C@(C.T@R)@C.T/(m*m)+U@H@U.T
        M=S0.T@P@S0-S1.T@P@S1-diss/scale-Q
        T=B.T@M@B
        L=P-coerc[:d,:d]/scale
        if supported_lower:
            Qlow=cp.reshape(np.column_stack([data[i]['Q'][:d,:d].ravel()
                           for i in lower_indices])@mu,(d,d),order='C')
            L=L-Qlow
        constraints += [T>>np.eye(d)/scale,L>>np.eye(d)/scale]
        Ps.append(P);Ts.append(T);Ls.append(L)
    objective=sum(cp.norm(P,'fro') for P in Ps)+cp.sum(lam)
    if supported_lower:objective=objective+cp.sum(mu)
    problem=cp.Problem(cp.Minimize(objective),constraints)
    started=time.monotonic()
    value=problem.solve(solver='CLARABEL',tol_gap_abs=1e-10,tol_gap_rel=1e-10,
                        tol_feas=1e-10,max_iter=400)
    out=dict(interval=[lo,hi],memory=m,status=problem.status,objective=float(value),
             seconds=time.monotonic()-started,certificate_scale=scale,
             method='constant-history-kernel parameterization',pure_lower=not supported_lower)
    if lam.value is not None:
        lower_indices=[i for i,r in enumerate(data) if r['i']<m and r['j']<m]
        out.update(multipliers=(scale*lam.value).tolist(),
                   lower_multipliers=((scale*mu.value).tolist() if supported_lower
                                      else [0]*len(lower_indices)),lower_indices=lower_indices,
                   P=[(scale*P.value).tolist() for P in Ps],
                   T=[(scale*T.value).tolist() for T in Ts],
                   lower_matrices=[(scale*L.value).tolist() for L in Ls],
                   min_eigenvalues_T=[float(scale*np.linalg.eigvalsh(T.value)[0]) for T in Ts],
                   min_eigenvalues_lower=[float(scale*np.linalg.eigvalsh(L.value)[0]) for L in Ls],
                   interpolation_indices=[{k:r[k] for k in ['name','i','j']} for r in data])
    return out


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--lo',type=float,default=1.88)
    p.add_argument('--hi',type=float,default=1.886);p.add_argument('--memory',type=int,default=20)
    p.add_argument('--scale',type=float,default=10000);p.add_argument('--output',required=True)
    p.add_argument('--supported-lower',action='store_true')
    a=p.parse_args()
    try:r=solve(a.lo,a.hi,a.memory,a.scale,a.supported_lower)
    except Exception as e:r=dict(interval=[a.lo,a.hi],memory=a.memory,error=type(e).__name__+': '+str(e))
    Path(a.output).write_text(json.dumps(r,indent=2)+'\n')
    print(json.dumps({k:v for k,v in r.items() if not isinstance(v,list) or k in
                     ['interval','min_eigenvalues_T','min_eigenvalues_lower']}),flush=True)
