#!/usr/bin/env python3
"""Independent checks for the second F3 research expansion.

The exact identities use SymPy rational algebra. Floating-point checks are
diagnostics, not proofs. A fixed seed and every reported maximum residual are
written to results_v2.json. Run with --output to choose an output directory.
"""
from __future__ import annotations
import argparse, json, platform
from pathlib import Path
import numpy as np
import scipy
from scipy.optimize import brentq, minimize
import sympy as sp

PAULI = np.array([[[0,1],[1,0]],[[0,-1j],[1j,0]],[[1,0],[0,-1]]],complex)
ID = np.eye(2)
SEED = 2406039452026

def bloch(a,b,T):
    M=np.eye(4,dtype=complex)
    for i in range(3):
        M += a[i]*np.kron(PAULI[i],ID)+b[i]*np.kron(ID,PAULI[i])
        for j in range(3): M += T[i,j]*np.kron(PAULI[i],PAULI[j])
    return M/4

def coordinates(M):
    a=np.array([np.trace(M@np.kron(P,ID)).real for P in PAULI])
    b=np.array([np.trace(M@np.kron(ID,P)).real for P in PAULI])
    T=np.array([[np.trace(M@np.kron(P,Q)).real for Q in PAULI] for P in PAULI])
    return a,b,T

def lower(c,r): return max(0,c*(1+r)-1)**2
def upper(c,r): return (1-r*r)*(3-4*c)+(c+(1-c)*r)**2
def joint_lower_state(c,r):
    x=max(0,c*(1+r)-1)
    a=c*(1-r*r)+r*x
    return bloch([0,0,a],[0,0,r],np.diag([0,0,x]))

def joint_upper_state(c,r):
    M=np.zeros((4,4),complex)
    M[0,0]=(1+r)/2
    M[1,1]=c*(1-r)/2
    M[3,3]=(1-c)*(1-r)/2
    M[0,3]=M[3,0]=np.sqrt((1-c)*(1-r*r))/2
    return M

def canonical_radial_state(c,t,alpha):
    aa=(1+c+t)/4; ab=(1+c-t)/4
    da=(1-c-t)/4; db=(1-c+t)/4
    return np.array([[aa,0,0,alpha*np.sqrt(max(0,aa*db))],
                     [0,ab,alpha*np.sqrt(max(0,ab*da)),0],
                     [0,alpha*np.sqrt(max(0,ab*da)),da,0],
                     [alpha*np.sqrt(max(0,aa*db)),0,0,db]],complex)

def quadratic_orbit(tau,k,K):
    """Global trust-region solution, including singular hard cases.

    Returns x, shift, value and case. K may be indefinite. The caller can
    verify the PSD shift, linear equation and complementarity independently.
    """
    d,U=np.linalg.eigh(K); h=U.T@k
    scale=max(1.,np.max(abs(d)),np.linalg.norm(h)); tol=1e-12*scale
    L=max(0.,-d[0]); den=d+L; pole=abs(den)<tol
    p=np.divide(h,den,out=np.zeros_like(h),where=~pole)
    hard=(np.linalg.norm(h[pole])<=tol and p@p<=1+1e-11)
    if hard:
        lam=L
        if L>tol:
            p[np.flatnonzero(pole)[0]]=np.sqrt(max(0,1-p@p))
            case='singular_boundary_hard_case'
        else: case='positive_semidefinite_interior_or_flat'
    else:
        def secular(z): return np.sum((h/(d+z))**2)-1
        hi=L+max(1.,np.linalg.norm(h)*2)
        while secular(hi)>0: hi=L+2*(hi-L)
        lo=np.nextafter(L,np.inf)
        # brentq works at the pole; nonzero h causes +infinity there.
        with np.errstate(divide='ignore',invalid='ignore'):
            lam=brentq(secular,lo,hi,xtol=5e-15,rtol=1e-14)
        p=h/(d+lam); case='regular_boundary'
    x=U@p
    return x,lam,float(tau+2*k@x-x@K@x),case

def exact_checks():
    c,r,p,x,alpha=sp.symbols('c r p x alpha',real=True)
    D=2-2*c-c*c; E=2-4*c+c*c
    H=(1-r*r)*(3-4*c)+(c+(1-c)*r)**2
    identities={
        'threshold_factor':sp.expand(H-1-(1-r)*(D*r+E)),
        'probability_polynomial':sp.expand(p*E+D*(1-p)-(2-2*(1+p)*c+(2*p-1)*c*c)),
        'minimum_probability_factor':sp.expand(1-(c*(1-r*r)+r*x)-r+x-(1-r)*(x-(c*(1+r)-1))),
        'positive_minimum_upper_gap':sp.expand((1-c+c*r)-(c*(1+r)-1)-2*(1-c)),
        'interpolated_correlation':sp.expand(
            2*alpha**2*(1-c)*(1-r*r)+(x+alpha*(1-c+c*r-x))**2
            -(x*x+2*x*(1-c+c*r-x)*alpha+
              ((1-c+c*r-x)**2+2*(1-c)*(1-r*r))*alpha**2)),
    }
    assert all(v==0 for v in identities.values())
    C=2/(1+p+sp.sqrt((1-p)**2+2))
    assert sp.simplify(2-2*(1+p)*C+(2*p-1)*C*C)==0
    cv=sp.Rational(3,4); rv=sp.Rational(1,2); xv=cv*(1+rv)-1
    av=cv*(1-rv*rv)+rv*xv
    diag=[(1+av+rv+xv)/4,(1+av-rv-xv)/4,(1-av+rv-xv)/4,(1-av-rv+xv)/4]
    return {'identities':{k:str(v) for k,v in identities.items()},
            'radical_threshold_polynomial':'0',
            'minimum_rational_example':{'c':str(cv),'r':str(rv),'diagonal':list(map(str,diag)),
              'minimum_F3_squared':str(xv*xv),'maximum_F3_squared':str(H.subs({c:cv,r:rv}))},
            'probability_threshold_endpoints':{'p=1/2':str(sp.simplify(C.subs(p,sp.Rational(1,2)))),
              'p=1':str(sp.radsimp(C.subs(p,1)))}}

def run(out:Path):
    rng=np.random.default_rng(SEED)
    record={'seed':SEED,'versions':{'python':platform.python_version(),'numpy':np.__version__,
      'scipy':scipy.__version__,'sympy':sp.__version__},'exact':exact_checks()}
    residual={'joint_min_slack':1.,'joint_max_slack':1.,'witness_min_eigenvalue':1.,
      'witness_centre_error':0.,'witness_value_error':0.,'radial_interval_error':0.,
      'kraus_effect_slack':1.,'kraus_success_error':0.,'kraus_output_error':0.,
      'triple_volume_slack':1.,'triple_volume_witness_error':0.}
    ranks={}
    for rank in range(1,5):
        ranks[str(rank)]=0
        for _ in range(500):
            X=rng.normal(size=(4,rank))+1j*rng.normal(size=(4,rank))
            M=X@X.conj().T; M/=np.trace(M)
            a,b,T=coordinates(M); r=np.linalg.norm(b)
            if r>=1-1e-10: continue
            c=np.linalg.norm(a-T@b)/(1-r*r); f=np.sum(T*T)
            residual['joint_min_slack']=min(residual['joint_min_slack'],f-lower(c,r))
            residual['joint_max_slack']=min(residual['joint_max_slack'],upper(c,r)-f)
            B=np.trace(M.reshape(2,2,2,2),axis1=0,axis2=2)
            ev,U=np.linalg.eigh(B)
            if ev.min()>1e-10:
                F=U@np.diag(1/np.sqrt(2*ev))@U.conj().T
                canonical=np.kron(ID,F)@M@np.kron(ID,F.conj().T)
                ca,cb,S=coordinates(canonical); cc=np.linalg.norm(ca)
                n=ca/cc if cc>1e-9 else np.array([0.,0.,1.])
                t=np.linalg.norm(S.T@n); tau=np.sum(S*S)
                cap=t/2*min(tau-t*t,1+2*t+2*t*t-cc*cc-tau)
                residual['triple_volume_slack']=min(residual['triple_volume_slack'],cap-abs(np.linalg.det(S)))
            ranks[str(rank)]+=1
    for c in [0,.1,.5,.6,2/3,.75,.99,1.]:
        for r in [0,.1,.5,.9,.999]:
            lo=joint_lower_state(c,r); hi=joint_upper_state(c,r)
            for alpha in [0,.2,.7,1.]:
                M=(1-alpha)*lo+alpha*hi
                a,b,T=coordinates(M)
                residual['witness_min_eigenvalue']=min(residual['witness_min_eigenvalue'],np.linalg.eigvalsh(M).min())
                residual['witness_centre_error']=max(residual['witness_centre_error'],abs(np.linalg.norm(a-T@b)/(1-r*r)-c))
                x=max(0,c*(1+r)-1)
                expected=2*alpha*alpha*(1-c)*(1-r*r)+(x+alpha*(1-c+c*r-x))**2
                residual['witness_value_error']=max(residual['witness_value_error'],abs(np.sum(T*T)-expected))
            for frac in [0,.3,1.]:
                t=(1-c)*frac
                for alpha in [0,.2,1.]:
                    M=canonical_radial_state(c,t,alpha); a,b,S=coordinates(M)
                    expected=t*t+alpha*alpha*(1-c*c+t*t)
                    residual['radial_interval_error']=max(residual['radial_interval_error'],abs(np.sum(S*S)-expected))
                    residual['witness_min_eigenvalue']=min(residual['witness_min_eigenvalue'],np.linalg.eigvalsh(M).min())
                aa=(1+c+t)/4; ab=(1+c-t)/4; ee=(1-c-t)/4; dd=(1-c+t)/4
                capU=aa*dd; capV=ab*ee
                for gamma in [0,.2,.7,1.]:
                    sval=(capU+capV)*gamma
                    w=np.sqrt(max(0,min(sval,capU))); v=np.sqrt(max(0,sval-capU))
                    M=np.array([[aa,0,0,w],[0,ab,v,0],[0,v,ee,0],[w,0,0,dd]],complex)
                    a,b,S=coordinates(M); tau=np.sum(S*S)
                    expected=t/2*min(tau-t*t,1+2*t+2*t*t-c*c-tau)
                    residual['triple_volume_witness_error']=max(residual['triple_volume_witness_error'],abs(abs(np.linalg.det(S))-expected))
                    residual['witness_min_eigenvalue']=min(residual['witness_min_eigenvalue'],np.linalg.eigvalsh(M).min())
            sigma=joint_upper_state(c,0)
            F=np.diag(np.sqrt([1+r,1-r]))
            K=F/np.sqrt(1+r)
            raw=np.kron(ID,K)@sigma@np.kron(ID,K.conj().T)
            success=np.trace(raw).real
            residual['kraus_effect_slack']=min(residual['kraus_effect_slack'],np.linalg.eigvalsh(ID-K.conj().T@K).min())
            residual['kraus_success_error']=max(residual['kraus_success_error'],abs(success-1/(1+r)))
            residual['kraus_output_error']=max(residual['kraus_output_error'],np.linalg.norm(raw/success-hi))
    record['matrix_checks']={'states_by_rank':ranks,'joint_witnesses':160,'residuals':residual}
    assert residual['joint_min_slack']>-1e-9 and residual['joint_max_slack']>-1e-9
    assert residual['witness_min_eigenvalue']>-1e-12
    assert residual['witness_centre_error']<1e-9
    assert residual['witness_value_error']<1e-12
    assert residual['radial_interval_error']<1e-12
    assert residual['kraus_output_error']<1e-12
    assert residual['triple_volume_slack']>-1e-9
    assert residual['triple_volume_witness_error']<1e-12
    examples=[('zero',np.zeros(3),np.zeros((3,3))),
      ('singular_PSD',np.array([.2,0,0]),np.diag([1,0,0])),
      ('hard_indefinite',np.array([0,.2,0]),np.diag([-1,1,2])),
      ('hard_degenerate',np.zeros(3),np.diag([-1,-1,2])),
      ('regular_indefinite',np.array([.2,.1,.3]),np.diag([-1,1,2])),
      ('positive_interior',np.array([.2,.1,0]),np.diag([1,2,3]))]
    for i in range(120):
        A=rng.normal(size=(3,3)); K=(A+A.T)/2; k=rng.normal(size=3)
        examples.append((f'random_{i}',k,K))
    orbit_res={'stationarity':0.,'complementarity':0.,'smallest_shift_eigenvalue':1.,
      'ball_excess':0.,'optimization_error':0.}; cases={}; named=[]
    for name,k,K in examples:
        x,lam,value,case=quadratic_orbit(.7,k,K); cases[case]=cases.get(case,0)+1
        orbit_res['stationarity']=max(orbit_res['stationarity'],np.linalg.norm((K+lam*np.eye(3))@x-k))
        orbit_res['complementarity']=max(orbit_res['complementarity'],abs(lam*(1-x@x)))
        orbit_res['smallest_shift_eigenvalue']=min(orbit_res['smallest_shift_eigenvalue'],np.linalg.eigvalsh(K+lam*np.eye(3)).min())
        orbit_res['ball_excess']=max(orbit_res['ball_excess'],x@x-1)
        # Three unrelated local optimizer starts are a diagnostic only.
        vals=[]
        for _ in range(3):
            y=rng.normal(size=3); y=y/max(1,np.linalg.norm(y))*rng.uniform(0,1)
            res=minimize(lambda z:-(.7+2*k@z-z@K@z),y,
                jac=lambda z:-2*k+2*K@z,method='SLSQP',
                constraints={'type':'ineq','fun':lambda z:1-z@z,'jac':lambda z:-2*z},
                options={'maxiter':300,'ftol':1e-12})
            if res.success: vals.append(-res.fun)
        if vals: orbit_res['optimization_error']=max(orbit_res['optimization_error'],abs(max(vals)-value))
        if not name.startswith('random'): named.append({'name':name,'x':x.tolist(),'lambda':lam,'value':value,'case':case})
    record['trust_region_checks']={'problems':len(examples),'cases':cases,'residuals':orbit_res,'named_cases':named}
    assert orbit_res['stationarity']<1e-9 and orbit_res['complementarity']<1e-9
    assert orbit_res['smallest_shift_eigenvalue']>-1e-10 and orbit_res['ball_excess']<1e-9
    assert orbit_res['optimization_error']<1e-7
    prob=[]
    for p in [.5,.55,.6,.75,.9,1.]:
        C=2/(1+p+np.sqrt((1-p)**2+2)); R=min(1.,1/p-1)
        for c in [max(0,C-.01),C,min(1,C+.01)]:
            D=2-2*c-c*c
            radius=min(R,c*(1-c)/D) if c<2/3 else R
            value=upper(c,radius)
            prob.append({'p':p,'c':c,'threshold':C,'radius':radius,'max_F3_squared':value})
            if c<C-1e-12: assert value>1+1e-12
            if c>C+1e-12: assert value<=1+1e-12
    record['probability_frontier']=prob
    record['status']='PASS'
    out.mkdir(parents=True,exist_ok=True)
    (out/'results_v2.json').write_text(json.dumps(record,indent=2)+'\n')
    print(json.dumps({'status':'PASS','matrix_residuals':residual,'trust_region_residuals':orbit_res},indent=2))

if __name__=='__main__':
    p=argparse.ArgumentParser(); p.add_argument('--output',type=Path,default=Path(__file__).resolve().parent)
    run(p.parse_args().output)
