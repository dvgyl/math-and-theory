"""Produce and audit exact rational periodic ADMM candidates.

This script uses Fraction arithmetic for every certification inequality;
no floating point result is presented as a proof.
"""
import json
from pathlib import Path
from fractions import Fraction as Q
import numpy as np


def certify(Z,V,tau):
    K=len(Z);n=len(Z[0]);Z=[[Q(t) for t in r] for r in Z];V=[[Q(t) for t in r] for r in V]
    X=[[Z[i][j]+V[i][j]-V[(i-1)%K][j] for j in range(n)] for i in range(K)]
    U=[[tau*t for t in r] for r in V]
    A=[[Z[(i-1)%K][j]-U[(i-1)%K][j]-X[i][j] for j in range(n)] for i in range(K)]
    B=[[X[i][j]+U[(i-1)%K][j]-Z[i][j] for j in range(n)] for i in range(K)]
    checks=[]
    for label,pts,nrm in [('C',X,A),('D',Z,B)]:
        for i in range(K):
            for j in range(K):
                if i!=j:
                    val=sum(nrm[i][k]*(pts[i][k]-pts[j][k]) for k in range(n))
                    checks.append((label,i,j,val))
    meanZ=[sum(Z[i][j] for i in range(K)) for j in range(n)]
    meanX=[sum(X[i][j] for i in range(K)) for j in range(n)]
    dist=sum((X[0][j]-Z[0][j])**2 for j in range(n))
    good=min(t[-1] for t in checks)>0 and not any(meanZ+meanX) and dist>0
    return {'good':good,'K':K,'n':n,'tau':str(tau),'Z':Z,'V':V,'X':X,'U':U,'A':A,'B':B,
            'checks':checks,'minimum_margin':min(t[-1] for t in checks),'residual_sq':dist}


def main():
    data=np.load(Path(__file__).resolve().parent / 'admm_cycle_candidate_K5_tau1.99.npz')
    G=(data['G']+data['G'].T)/2
    ev,Qv=np.linalg.eigh(G);F=Qv[:,ev>1e-7]*np.sqrt(ev[ev>1e-7])
    Z=data['Z']@F;V=(data['U']@F)/float(data['tau'])
    rng=np.random.default_rng(503)
    best=None
    for scale in [20,30,40,50,60,80,100,150,200,300,500,1000,2000,5000]:
        for trial in range(250 if scale<200 else 1):
            rot=np.eye(Z.shape[1]) if trial==0 else np.linalg.qr(rng.normal(size=(Z.shape[1],Z.shape[1])))[0]
            z=np.rint(scale*Z@rot).astype(int);v=np.rint(scale*V@rot).astype(int)
            z[-1]=-z[:-1].sum(axis=0);v[-1]=-v[:-1].sum(axis=0)
            out=certify(z,v,Q(199,100))
            if out['good']:
                best=out;print('EXACT CANDIDATE',scale,trial,'margin',out['minimum_margin'])
                print('Z',z.tolist());print('V',v.tolist());break
        if best is not None:break
    if best is None:raise RuntimeError('No candidate rationalization certified')
    outpath=(Path(__file__).resolve().parent / 'admm_exact_K5_tau199over100.json')
    outpath.write_text(json.dumps(best,indent=2,default=str))
    print('WROTE',outpath)


if __name__=='__main__':main()
