#!/usr/bin/env python3
"""Compare the full coupling SDP and exact two-cap amplitude SDP.

Solver outputs are approximate diagnostics. They do not replace the exact
proof or Lean's bound equivalence. Marginal transposes are deliberate.
"""
from pathlib import Path
import json,time,warnings
import cvxpy as cp
import numpy as np

HERE=Path(__file__).resolve().parent

def state(rng,d,rank=None):
    rank=d if rank is None else rank
    G=rng.normal(size=(d,rank))+1j*rng.normal(size=(d,rank))
    M=G@G.conj().T;return M/np.trace(M)

def solve_case(A,B,X):
    original_shape=list(X.shape)
    X=X/np.linalg.norm(X)
    original_target_rank=int(np.linalg.matrix_rank(X))
    # Exact support reduction is mathematically necessary for robust numerical
    # treatment of singular marginals. Every feasible coupling is supported
    # on supp(A) tensor supp(B). Do NOT renormalize the projected target.
    av,au=np.linalg.eigh(A);bv,bu=np.linalg.eigh(B)
    ia=av>1e-10;ib=bv>1e-10
    X=au[:,ia].conj().T@X@bu[:,ib].conj()
    A=np.diag(av[ia]);B=np.diag(bv[ib])
    m,n=X.shape;x=X.reshape(-1)
    rho=cp.Variable((m*n,m*n),hermitian=True)
    redA=cp.bmat([[sum(rho[i*n+j,k*n+j] for j in range(n)) for k in range(m)] for i in range(m)])
    redB=cp.bmat([[sum(rho[i*n+j,i*n+l] for i in range(m)) for l in range(n)] for j in range(n)])
    big=cp.Problem(cp.Maximize(cp.real(cp.trace(np.outer(x,x.conj())@rho))),[rho>>0,redA==A,redB==B])
    W=cp.Variable((m,n),complex=True)
    small=cp.Problem(cp.Maximize(cp.real(cp.trace(X.conj().T@W))),[
        cp.bmat([[A,W],[W.H,np.eye(n)]])>>0,
        cp.bmat([[np.eye(m),W],[W.H,B.T]])>>0])
    settings=dict(solver='CLARABEL',tol_gap_abs=1e-9,tol_feas=1e-9,tol_gap_rel=1e-9,max_iter=200)
    with warnings.catch_warnings(record=True) as ws:
        v1=big.solve(**settings);v2=small.solve(**settings)
    assert rho.value is not None and W.value is not None,(big.status,small.status)
    ww=W.value;A0=A-ww@ww.conj().T;B0=B-(ww.conj().T@ww).T;delta=float(np.trace(A0).real)
    record={'original_dimensions':original_shape,'support_dimensions':[m,n],
            'target_schmidt_rank':original_target_rank,
            'projected_target_norm':float(np.linalg.norm(X)),
            'full_status':big.status,'reduced_status':small.status,'full_value':float(v1),
            'amplitude_value':float(v2),'squared_reduced_value':float(v2*v2),
            'absolute_value_difference':float(abs(v1-v2*v2)),
            'residual_A_min_eigenvalue':float(np.linalg.eigvalsh(A0).min()),
            'residual_B_min_eigenvalue':float(np.linalg.eigvalsh(B0).min()),
            'solver_warnings':[str(w.message) for w in ws]}
    if delta>1e-7:
        residual=np.kron(A0,B0)/delta
        completion=np.outer(ww.reshape(-1),ww.reshape(-1).conj())+residual
        record['residual_target_overlap']=float(np.vdot(x,residual@x).real)
        record['completion_value_difference']=float(abs(np.vdot(x,completion@x).real-v1))
        record['completion_min_eigenvalue']=float(np.linalg.eigvalsh(completion).min())
    return record

def rank_sharpness():
    rows=[]
    for d in range(2,11):
        eps=1/(3*d);a=np.full(d,1/d-eps);a[0]=1/d+(d-1)*eps;b=np.ones(d)/d
        m=np.minimum(a,b);z=np.zeros(d*d);z[np.arange(d)*(d+1)]=np.sqrt(m)
        R=np.zeros((d*d,d*d))
        for j in range(1,d):R[j,j]=eps
        rho=np.outer(z,z)+R;rank=int((np.linalg.eigvalsh(rho)>1e-10).sum())
        phi=np.zeros(d*d);phi[np.arange(d)*(d+1)]=1/np.sqrt(d)
        rows.append({'d':d,'marginal_min_eigenvalue':float(min(a.min(),b.min())),
                     'unique_optimizer_rank':rank,'bell_overlap':float(phi@rho@phi),
                     'target_bound':float(np.sqrt(m).sum()**2/d)})
        assert rank==d
    return rows

def main():
    rng=np.random.default_rng(2026110304);rows=[];start=time.monotonic()
    for m,n in [(2,2),(2,3),(3,3),(3,4)]:
        for kind in ['full','rank_one_target','singular_A','singular_B']:
            A=state(rng,m,1 if kind=='singular_A' else None)
            B=state(rng,n,1 if kind=='singular_B' else None)
            X=rng.normal(size=(m,n))+1j*rng.normal(size=(m,n))
            if kind=='rank_one_target':
                u=rng.normal(size=m)+1j*rng.normal(size=m);v=rng.normal(size=n)+1j*rng.normal(size=n)
                X=np.outer(u,v)
            rec=solve_case(A,B,X);rec['case']=kind;rows.append(rec)
            print(m,n,kind,rec['absolute_value_difference'],flush=True)
    result={'seed':2026110304,'cvxpy_version':cp.__version__,'solver':'CLARABEL',
            'scope':'Approximate independent SDP comparisons, not exact certificates',
            'singular_handling':'Both SDPs are exactly compressed to the actual marginal supports. The projected target is not renormalized.',
            'initial_uncompressed_diagnostic':'A direct singular-marginal run produced a 0.00032029232953702247 discrepancy and a CLARABEL failure. This was solver ill-conditioning, resolved by exact support reduction; the raw diagnostic log is retained.',
            'cases':rows,'maximum_value_difference':max(r['absolute_value_difference'] for r in rows),
            'rank_sharpness':rank_sharpness(),'seconds':round(time.monotonic()-start,3)}
    assert result['maximum_value_difference']<5e-5,result['maximum_value_difference']
    (HERE/'sdp_reduction_results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ['cases','rank_sharpness']},indent=2))

if __name__=='__main__':main()
