#!/usr/bin/env python3
"""Independent numerical/exact checks for the F3 envelope and geometric refinements.

Run: python3 calculations/reproduce.py --samples 20000
Dependencies: numpy, matplotlib. No input data or network required.
Floating point stress tests are diagnostics; universal proofs are in the report/Lean.
"""
from __future__ import annotations
import argparse
from fractions import Fraction as R
import json
from pathlib import Path
import platform
import numpy as np

ROOT = Path(__file__).resolve().parents[1]
I = np.eye(2, dtype=complex)
P = np.array([[[0,1],[1,0]], [[0,-1j],[1j,0]], [[1,0],[0,-1]]], dtype=complex)
PA = np.array([np.kron(s,I) for s in P])
PB = np.array([np.kron(I,s) for s in P])
PP = np.array([[np.kron(s,t) for t in P] for s in P])
YY = np.kron(P[1],P[1])

def obs(rho):
    a = np.einsum('ij,kji->k',rho,PA).real
    b = np.einsum('ij,kji->k',rho,PB).real
    T = np.einsum('ij,klji->kl',rho,PP).real
    return a,b,T

def ptrA(rho):
    return np.trace(rho.reshape(2,2,2,2),axis1=1,axis2=3)

def ptrB(rho):
    return np.trace(rho.reshape(2,2,2,2),axis1=0,axis2=2)

def sqrt_psd(A, inverse=False):
    eig,U = np.linalg.eigh(A)
    if inverse and eig.min() <= 0: raise ValueError('Singular positive square root')
    d = 1/np.sqrt(eig) if inverse else np.sqrt(np.maximum(eig,0))
    return (U*d)@U.conj().T

def canonical(rho):
    F = sqrt_psd(2*ptrB(rho),inverse=True)
    K = np.kron(I,F)
    return K@rho@K

def witness(c,r):
    w = np.array([0,np.sqrt(1+r),np.sqrt((1-c)*(1-r)),0])
    rho = np.outer(w,w).astype(complex)/2
    rho[0,0] += c*(1-r)/2
    return rho

def radial_witness(c,t):
    ap,am,dm,dp = (1+c+t)/4,(1+c-t)/4,(1-c-t)/4,(1-c+t)/4
    rho = np.diag([ap,am,dm,dp]).astype(complex)
    rho[0,3] = rho[3,0] = np.sqrt(max(0,ap*dp))
    rho[1,2] = rho[2,1] = np.sqrt(max(0,am*dm))
    return rho

def quadratic(c,r): return (1-r*r)*(3-4*c)+(c+(1-c)*r)**2
def D(c): return 2-2*c-c*c
def envelope(c): return 1+(2-3*c)**2/D(c) if c<2/3 else 1
def rstar(c): return c*(1-c)/D(c)

def axis_to_z(v):
    if np.linalg.norm(v) < 1e-13: return I.copy()
    _,V = np.linalg.eigh(np.einsum('k,kij->ij',v,P))
    return V[:,[1,0]].conj().T

def align_canonical(sigma):
    a,_,_ = obs(sigma)
    U = np.kron(axis_to_z(a),I)
    s = U@sigma@U.conj().T
    _,_,T = obs(s)
    V = np.kron(I,axis_to_z(T[2]))
    s = V@s@V.conj().T
    phase = np.angle(s[0,3])
    W = np.kron(np.diag([np.exp(-1j*phase),1]),I)
    return W@s@W.conj().T

def exact_checks():
    out = []
    for c in [R(0),R(1,2),R(3,5),R(53,80),R(2,3)]:
        r = c*(1-c)/D(c)
        f = quadratic(c,r)
        assert D(c)+(2-3*c)**2-D(c)*quadratic(c,r)==0
        out.append(dict(c=str(c),r_star=str(r),squared_F3=str(f),attained=(c<R(2,3))))
    # Exact evaluations corroborate algebra; Lean proves identities for all reals.
    count = 0
    for p in range(21):
        c=R(p,20)
        for k in range(21):
            r=R(k,20)
            assert 1-quadratic(c,r)==(1-r)**2*(4*c-2-c*c)+r*(1-r)*(6*c-4)
            assert D(c)+(2-3*c)**2-D(c)*quadratic(c,r)==(D(c)*r-c*(1-c))**2
            count += 1
    return dict(examples=out,rational_identity_evaluations=count)

def run_checks(samples,seed):
    rng=np.random.default_rng(seed)
    maxima=dict(envelope_excess=-np.inf,coordinate_centre_error=0.,filter_identity_error=0.,
                spinflip_identity_error=0.,geometric_slack_identity_error=0.,
                stability_excess=-np.inf,stability_normal_form_error=0.)
    minima=dict(general_LMI_eigenvalue=np.inf,radial_slack=np.inf,radial_support_gap=np.inf)
    scatter=[]
    rank_counts={str(i):0 for i in range(1,5)}
    for k in range(samples):
        rank=k%4+1
        X=rng.normal(size=(4,rank))+1j*rng.normal(size=(4,rank))
        rho=X@X.conj().T; rho/=np.trace(rho).real
        rank_counts[str(rank)]+=1
        a,b,T=obs(rho); r=np.linalg.norm(b); f=np.sum(T*T)
        sigma=canonical(rho); cv,bb,S=obs(sigma); c=np.linalg.norm(cv)
        maxima['coordinate_centre_error']=max(maxima['coordinate_centre_error'],np.linalg.norm(cv-(a-T@b)/(1-r*r)))
        maxima['envelope_excess']=max(maxima['envelope_excess'],f-envelope(c))
        maxima['filter_identity_error']=max(maxima['filter_identity_error'],abs(f-((1-r*r)*(np.sum(S*S)-c*c)+a@a)))
        MA=(1+a@a-b@b-f)*np.eye(3)+2*(T@T.T-np.outer(a,a))
        minima['general_LMI_eigenvalue']=min(minima['general_LMI_eigenvalue'],np.linalg.eigvalsh(MA).min())
        n=rng.normal(size=3); n/=np.linalg.norm(n)
        U=np.kron(np.einsum('k,kij->ij',n,P),I)@YY
        flip=U@rho.T@U.conj().T
        overlap=4*np.trace(rho@flip).real
        expr=1+a@a-b@b-f+2*np.linalg.norm(T.T@n)**2-2*(a@n)**2
        maxima['spinflip_identity_error']=max(maxima['spinflip_identity_error'],abs(overlap-expr))
        if c>1e-10:
            n=cv/c; q=np.linalg.norm(S.T@n)**2
            tau=1-c*c+2*q-np.sum(S*S)
            minima['radial_slack']=min(minima['radial_slack'],tau)
            minima['radial_support_gap']=min(minima['radial_support_gap'],(1-c)**2-q)
            if c<2/3 and r>1e-12:
                y=cv+S@(b/r)
                decomp=(D(c)*(r-rstar(c))**2+(1-r*r)*(2*((1-c)**2-q)+tau)
                       +r*(r+c*(1-r))*(1-y@y)+r*c*(1-r)*np.sum((y-n)**2))
                maxima['geometric_slack_identity_error']=max(maxima['geometric_slack_identity_error'],abs(envelope(c)-f-decomp))
        if c<1-1e-10:
            ss=align_canonical(sigma)
            a2,b2,T2=obs(ss)
            t=max(0.,T2[2,2]); delta=3-4*c+c*c-np.sum(S*S)
            target=radial_witness(c,1-c)
            dist=np.abs(np.linalg.eigvalsh(ss-target)).sum()
            bound=(.5+(2+c)/(1-c+t))*max(delta,0.)
            maxima['stability_excess']=max(maxima['stability_excess'],dist*dist-bound)
            maxima['stability_normal_form_error']=max(maxima['stability_normal_form_error'],abs(ss[0,1]),abs(ss[2,3]),abs(ss[0,2]+ss[1,3]))
        if k%max(1,samples//4000)==0: scatter.append([float(c),float(f),rank])
    # Explicit sharp families exercise the boundary, where generic sampling is weak.
    witness_error=radial_error=radial_min_eig=0.
    for c in np.linspace(0,1,101):
        for r in [0.,.2,.7,.99,.999999]:
            w=witness(c,r); aa,bb,TT=obs(w)
            witness_error=max(witness_error,abs(np.sum(TT*TT)-quadratic(c,r)))
            if c<1-1e-12:
                witness_error=max(witness_error,abs(np.linalg.norm((aa-TT@bb)/(1-bb@bb))-c))
        for frac in np.linspace(0,1,21):
            t=frac*(1-c); w=radial_witness(c,t); aa,bb,TT=obs(w)
            radial_error=max(radial_error,abs(np.sum(TT*TT)-(1-c*c+2*t*t)),np.linalg.norm(bb),abs(aa[2]-c))
            radial_min_eig=min(radial_min_eig,np.linalg.eigvalsh(w).min())
    assert maxima['envelope_excess'] < 1e-7
    assert minima['general_LMI_eigenvalue'] > -1e-7
    assert maxima['stability_excess'] < 1e-6
    assert maxima['spinflip_identity_error'] < 1e-8
    assert maxima['geometric_slack_identity_error'] < 1e-7
    return dict(seed=seed,samples=samples,rank_counts=rank_counts,maxima=maxima,minima=minima,
                sharp_family_max_error=witness_error,radial_family_max_error=radial_error,
                radial_family_min_eigenvalue=radial_min_eig,scatter=scatter)

def plot(result):
    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    plt.rcParams.update({'font.family':'DejaVu Sans','font.size':10,'axes.spines.top':False,'axes.spines.right':False})
    fig,ax=plt.subplots(figsize=(7.5,4.5),layout='constrained')
    a=np.array(result.pop('scatter'))
    ax.scatter(a[:,0],a[:,1],s=4,c='#94a3b8',alpha=.25,rasterized=True,label='Random PSD states (ranks 1–4)')
    cs=np.linspace(0,2/3,400)
    ax.plot(cs,[envelope(x) for x in cs],color='#1d4ed8',lw=2.5,label='Sharp attained envelope')
    ax.plot([2/3,1],[1,1],'--',color='#1d4ed8',lw=2,label=r'Supremum; not attained for $2/3\leq c<1$')
    ax.scatter([2/3],[1],s=45,facecolor='white',edgecolor='#1d4ed8',zorder=5)
    ax.scatter([1],[1],s=35,color='#1d4ed8',zorder=5)
    c2=np.linspace(0,1,400)
    ax.plot(c2,3-4*c2+c2*c2,color='#b45309',lw=1.4,label='Canonical maximum')
    ax.axvline(2/3,color='#475569',ls=':',lw=1)
    ax.set(xlabel='Steering ellipsoid centre length $c$',ylabel='Squared correlation value $F_3^2$',xlim=(0,1.01),ylim=(-.03,3.08))
    ax.legend(fontsize=8,loc='upper right')
    dest=ROOT/'figures'; dest.mkdir(exist_ok=True)
    fig.savefig(dest/'envelope.png',dpi=180); fig.savefig(dest/'envelope.pdf')
    plt.close(fig)

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--samples',type=int,default=20000);parser.add_argument('--seed',type=int,default=240603945)
    args=parser.parse_args()
    result=run_checks(args.samples,args.seed);plot(result)
    result['exact_checks']=exact_checks()
    result['environment']={'python':platform.python_version(),'numpy':np.__version__}
    result['status']='PASS; numerical checks supplement the proofs, not replace them'
    out=ROOT/'calculations'/'results.json';out.write_text(json.dumps(result,indent=2,default=float)+'\n')
    print(json.dumps(result,indent=2,default=float))

if __name__=='__main__':main()
