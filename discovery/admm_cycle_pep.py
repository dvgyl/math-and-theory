"""Exploration of genuine periodic orbits for dual-relaxed, two-block ADMM.

The SDP is a convex interpolation feasibility test, not a proof of convergence.
Any positive numerical cycle requires a separate exact certificate.

For a period K, independent vectors are z_i,u_i (i modulo K), and
    x_i = z_i + (u_i-u_{i-1})/tau,
    a_i = z_{i-1}-u_{i-1}-x_i,
    b_i = x_i+u_{i-1}-z_i.
We impose a_i in N_C(x_i), b_i in N_D(z_i), where C and D are the
convex hulls of the sampled x and z points. Centering puts 0 in both hulls.
These conditions make the sampled points an exact ADMM cycle for indicators
of C and D if the Gram matrix and inequalities can be certified exactly.
"""
import argparse, json, time
from pathlib import Path
import cvxpy as cp
import numpy as np


def solve(K, tau, cyclic=True):
    E=np.eye(2*K); Z=E[:K]; U=E[K:]
    X=np.array([Z[i]+(U[i]-U[(i-1)%K])/tau for i in range(K)])
    A=np.array([Z[(i-1)%K]-U[(i-1)%K]-X[i] for i in range(K)])
    B=np.array([X[i]+U[(i-1)%K]-Z[i] for i in range(K)])
    G=cp.Variable((2*K,2*K),symmetric=True)
    slack=cp.Variable()
    constraints=[G >> 0, cp.trace(G)==1,
                 G @ Z.sum(axis=0)==0, G @ U.sum(axis=0)==0]
    if cyclic:
        shift=np.r_[np.roll(np.arange(K),1), K+np.roll(np.arange(K),1)]
        constraints.append(G==G[np.ix_(shift,shift)])
    def ip(a,b): return cp.sum(cp.multiply(np.outer(a,b),G))
    for points, normals in [(X,A),(Z,B)]:
        for i in range(K):
            for j in range(K):
                if i!=j: constraints.append(ip(normals[i],points[j]-points[i])+slack <= 0)
    problem=cp.Problem(cp.Maximize(slack),constraints)
    t=time.monotonic()
    val=problem.solve(solver='CLARABEL',tol_gap_abs=1e-11,tol_gap_rel=1e-11,
                      tol_feas=1e-11,max_iter=300)
    if G.value is not None:
        residual=sum(float((X[i]-Z[i]) @ G.value @ (X[i]-Z[i])) for i in range(K))
        evals=np.linalg.eigvalsh(G.value)
    else: residual=None;evals=[]
    out=dict(K=K,tau=tau,slack=val,status=problem.status,residual=residual,
             eigenvalues=list(evals),seconds=time.monotonic()-t)
    print(json.dumps(out),flush=True)
    if val is not None and val > 1e-8:
        p=Path(__file__).resolve().parent / f'admm_cycle_candidate_K{K}_tau{tau}.npz'
        np.savez(p,G=G.value,X=X,Z=Z,U=U,A=A,B=B,tau=tau,K=K,slack=val)
        print('CANDIDATE',p,flush=True)
    return out


def main():
    p=argparse.ArgumentParser();p.add_argument('--K',type=int,nargs='+',default=[2,3,4,5,6,8,10,12]);p.add_argument('--tau',type=float,nargs='+',default=[1.9,1.99])
    a=p.parse_args();results=[]
    for tau in a.tau:
        for K in a.K:results.append(solve(K,tau))
    (Path(__file__).resolve().parent / 'admm_cycle_pep.json').write_text(json.dumps(results,indent=2))

if __name__=='__main__':main()
