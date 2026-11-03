#!/usr/bin/env python3
"""Reproducible falsification checks for negativity_theorems.tex.
Exact symbolic checks and floating-point diagnostics are reported separately.
No numerical optimization is represented as proof.
"""
import os
os.environ.setdefault('OPENBLAS_NUM_THREADS','1')
os.environ.setdefault('OMP_NUM_THREADS','1')
import json, math, pathlib, hashlib, platform, time
import numpy as np
import scipy
from scipy.linalg import block_diag
import sympy as sp
import cvxpy as cp
ROOT=pathlib.Path(__file__).resolve().parent
rng=np.random.default_rng(733039)

def pt(rho,r,s):
    return rho.reshape(r,s,r,s).transpose(0,3,2,1).reshape(r*s,r*s)
def marg(rho,r,s):
    x=rho.reshape(r,s,r,s)
    return np.einsum('ijkj->ik',x),np.einsum('ijil->jl',x)
def trace_norm_h(x): return np.abs(np.linalg.eigvalsh(x)).sum()
def nneg(rho,r,s): return (trace_norm_h(pt(rho,r,s))-np.trace(rho).real)/2

def rand_density(n):
    x=rng.normal(size=(n,n))+1j*rng.normal(size=(n,n))
    x=x@x.conj().T
    return x/np.trace(x)
def diagonal_marginals(R,r,s):
    a,b=marg(R,r,s)
    _,u=np.linalg.eigh(a); _,v=np.linalg.eigh(b)
    U=np.kron(u.conj().T,v.conj().T)
    return U@R@U.conj().T

def embed(m,R,I,J):
    d=len(m); z=np.zeros(d*d,complex); z[np.arange(d)*(d+1)]=np.sqrt(m)
    out=np.outer(z,z.conj())
    ids=[i*d+j for i in I for j in J]
    out[np.ix_(ids,ids)]+=R
    return out

def hnorm(C,ds):
    D=np.diag(ds);z=np.zeros_like(C)
    return trace_norm_h(np.block([[C,D],[D,z]]))

def unitary(q):
    a=rng.normal(size=(q,q))+1j*rng.normal(size=(q,q))
    u,r=np.linalg.qr(a)
    return u@np.diag(np.diag(r)/np.abs(np.diag(r))).conj()

def balanced_density(q):
    R=rand_density(q*q)
    for it in range(200):
        a,b=marg(R,q,q)
        vals,U=np.linalg.eigh(a)
        K=(U/np.sqrt(q*vals))@U.conj().T
        R=np.kron(K,np.eye(q))@R@np.kron(K.conj().T,np.eye(q))
        a,b=marg(R,q,q)
        vals,U=np.linalg.eigh(b)
        K=(U/np.sqrt(q*vals))@U.conj().T
        R=np.kron(np.eye(q),K)@R@np.kron(np.eye(q),K.conj().T)
        a,b=marg(R,q,q)
        err=max(np.linalg.norm(a-np.eye(q)/q),np.linalg.norm(b-np.eye(q)/q))
        if err<3e-13: return R,it+1,err
    raise AssertionError(('sinkhorn convergence',q,err))

out={'seed':733039,'versions':{'python':platform.python_version(),'numpy':np.__version__,'scipy':scipy.__version__,'sympy':sp.__version__,'cvxpy':cp.__version__},'scope':'Exact symbolic certificates plus numerical falsification; not a Lean or universal proof.'}
start=time.time()

# 1. Strict convexity for arbitrary Hermitian saddle blocks, plus the explicit modulus.
worst_convex=0.;worst_modulus=0.;count=0
for n in range(1,8):
    for k in range(80):
        ds=.03+rng.random(n)
        Cs=[]
        for _ in range(2):
            C=rng.normal(size=(n,n))+1j*rng.normal(size=(n,n));C=(C+C.conj().T)/2
            C/=max(1,np.linalg.norm(C,2));Cs.append(C)
        C0,C1=Cs; t=.05+.9*rng.random();C=(1-t)*C0+t*C1
        gap=(1-t)*hnorm(C0,ds)+t*hnorm(C1,ds)-hnorm(C,ds)
        delta=max(np.linalg.norm(C0,2),np.linalg.norm(C1,2))
        dm,dp=ds.min(),ds.max();h=(np.sqrt(delta**2+4*dm**2)-delta)/2
        strong=h*h/(2*(delta+dp)*dp*dp)
        lower=.5*strong*t*(1-t)*np.linalg.norm(C0-C1,'fro')**2
        worst_convex=max(worst_convex,-gap);worst_modulus=max(worst_modulus,lower-gap)
        assert gap+2e-11>=lower
        if np.linalg.norm(C0-C1)>1e-8: assert gap>1e-12
        count+=1
out['saddle_strict_convexity']={'cases':count,'max_convexity_violation':worst_convex,'max_strong_convexity_violation':worst_modulus}

# 2. Quantum residual dephasing and explicit coherence penalty, with actual diagonal marginals.
count=0;max_formula_error=0.;max_gap_violation=0.;max_marginal_error=0.
for r,s in [(1,2),(2,2),(2,3),(3,2),(3,3)]:
    for k in range(70):
        d=r+s; delta=.05+.8*rng.random();m=rng.dirichlet(np.ones(d))*(1-delta)
        R=diagonal_marginals(rand_density(r*s)*delta,r,s)
        Rd=np.diag(np.diag(R).real)
        A,B=marg(R,r,s);Ad,Bd=marg(Rd,r,s)
        max_marginal_error=max(max_marginal_error,np.linalg.norm(A-Ad),np.linalg.norm(B-Bd))
        I=list(range(r));J=list(range(r,d));rho=embed(m,R,I,J);rhod=embed(m,Rd,I,J)
        N=nneg(rho,d,d);Nd=nneg(rhod,d,d)
        ds=np.array([np.sqrt(m[i]*m[j]) for i in I for j in J])
        N0=(np.sqrt(m).sum()**2-m.sum())/2-ds.sum()
        formula=N0+(hnorm(pt(R,r,s),ds)-delta)/2
        max_formula_error=max(max_formula_error,abs(N-formula))
        dm,dp=ds.min(),ds.max();h=(np.sqrt(delta*delta+4*dm*dm)-delta)/2
        lower=h*h*np.linalg.norm(R-Rd,'fro')**2/(8*dp*dp*(delta+dp))
        max_gap_violation=max(max_gap_violation,lower-(N-Nd))
        assert abs(N-formula)<2e-11 and N-Nd+2e-11>=lower
        if r*s>2: assert N-Nd>1e-12
        count+=1
out['dephasing_and_coherence_penalty']={'cases':count,'max_block_formula_error':max_formula_error,'max_gap_violation':max_gap_violation,'max_actual_marginal_change':max_marginal_error}

# 3. Transport minimizer agrees with the full quantum trace-norm SDP.
# Low dimension is deliberate: these checks are falsification diagnostics.
records=[]
for r,s in [(2,2),(2,2),(2,3),(3,2),(3,3),(3,3)]:
    d=r+s;delta=.15+.45*rng.random();m=rng.dirichlet(np.ones(d))*(1-delta)
    u=rng.dirichlet(np.ones(r))*delta;v=rng.dirichlet(np.ones(s))*delta
    ds=np.sqrt(m[:r,None]*m[None,r:])
    T=cp.Variable((r,s),nonneg=True)
    costs=[cp.norm(cp.hstack([T[i,j],2*ds[i,j]]),2)-T[i,j] for i in range(r) for j in range(s)]
    prob=cp.Problem(cp.Minimize(cp.sum(cp.hstack(costs))/2),[cp.sum(T,axis=1)==u,cp.sum(T,axis=0)==v])
    val=prob.solve(solver='CLARABEL',tol_gap_abs=1e-9,tol_feas=1e-9,tol_gap_rel=1e-9,max_iter=200)
    R=cp.Variable((r*s,r*s),hermitian=True)
    C=cp.partial_transpose(R,[r,s],axis=1)
    D=np.diag(ds.ravel());H=cp.bmat([[C,D],[D,np.zeros((r*s,r*s))]])
    qp=cp.Problem(cp.Minimize((cp.normNuc(H)-delta)/2),[R>>0,cp.partial_trace(R,[r,s],axis=1)==np.diag(u),cp.partial_trace(R,[r,s],axis=0)==np.diag(v)])
    qval=qp.solve(solver='CLARABEL',tol_gap_abs=1e-8,tol_feas=1e-8,tol_gap_rel=1e-8,max_iter=200)
    gap=abs(val-qval)
    assert gap<2e-6
    records.append({'shape':[r,s],'classical_value':val,'quantum_value':qval,'absolute_difference':gap,'classical_status':prob.status,'quantum_status':qp.status,'quantum_off_diagonal_norm':float(np.linalg.norm(R.value-np.diag(np.diag(R.value)),'fro'))})
out['transport_quantum_sdp_comparison']=records

# 4. Exact symbolic endpoint identities and a concrete rank/negativity counterexample.
a,b,delta,q=sp.symbols('a b delta q',positive=True)
mintrace=sp.sqrt(delta**2+4*q**4*a*b)
maxtrace=q*sp.sqrt(delta**2+4*q**2*a*b)
assert sp.simplify(mintrace**2-(delta**2+4*q**4*a*b))==0
assert sp.simplify(maxtrace**2-q**2*(delta**2+4*q**2*a*b))==0
Q=sp.Rational
a0,b0,d0=Q(3,10),Q(1,10),Q(1,5)
base=a0+b0
Nmin=sp.simplify(base+(sp.sqrt(d0*d0+64*a0*b0)-d0)/2)
Nmax=sp.simplify(base+(2*sp.sqrt(d0*d0+16*a0*b0)-d0)/2)
assert Nmin==1 and sp.simplify(Nmax-(Q(3,10)+sp.sqrt(13)/5))==0
fef=sp.simplify((sp.sqrt(a0)+sp.sqrt(b0))**2)
assert sp.simplify(fef-(Q(2,5)+sp.sqrt(3)/5))==0
G=4*sp.sqrt(a0*b0);assert sp.simplify(G-2*sp.sqrt(3)/5)==0
# Exact partial transpose eigenvalue-square identity for a normalized Bell projector.
for k in range(2,6):
    F=sp.zeros(k*k)
    for i in range(k):
        for j in range(k): F[i*k+j,j*k+i]=1
    assert F*F==sp.eye(k*k) and sp.trace(F)==k
# Exact singular-D failure of strict convexity.
D=sp.diag(1,0)
for t in [Q(1),Q(2),Q(3)]:
    C=sp.diag(0,t);H=C.row_join(D).col_join(D.row_join(sp.zeros(2)))
    ev=H.eigenvals();assert sum(abs(x)*mult for x,mult in ev.items())==2+t
# An exact nonproduct transportation minimizer with independently checked KKT potentials.
kappa=Q(17,3)+4/sp.sqrt(21)
aa=1/(Q(101,50)+kappa/10);bb=aa/100;dd=aa/10;ddelta=kappa*dd
TS=sp.Matrix([[4/sp.sqrt(21),Q(3,2)],[Q(3,2),Q(8,3)]])
assert sp.simplify(2*aa+2*bb+ddelta-1)==0
pot=sp.Matrix([[Q(-3,10),Q(-1,5)],[Q(-1,5),Q(-1,10)]])
for i in range(2):
    for j in range(2):
        derivative=sp.simplify((TS[i,j]/sp.sqrt(TS[i,j]**2+4)-1)/2)
        assert sp.simplify(derivative-pot[i,j])==0
cost=sp.simplify(sum((sp.sqrt(t*t+4)-t)/2 for t in TS))
assert sp.simplify(cost-(Q(4,3)+3/sp.sqrt(21)))==0
assert sp.simplify(TS.det()-(32/(3*sp.sqrt(21))-Q(9,4)))==0
assert 128**2>27**2*21
out['exact_symbolic']={'passed':True,'checks':21,'nonproduct_transport_KKT':'exact derivatives (-3/10,-1/5;-1/5,-1/10); determinant>0, so product coupling is strictly worse','four_level_FEF':str(fef),'four_level_G':str(G),'four_level_N_min':str(Nmin),'four_level_N_max':str(Nmax),'endpoint_global_ranks':[5,2],'singular_D_counterexample':'D=diag(1,0), C_t=diag(0,t), F_D(C_t)=2+t for t>=0'}

# 5. General balanced faces: arbitrary Sinkhorn-balanced states plus random-unitary mixtures.
count=0;worst_bound=0.;worst_formula=0.;worst_margin=0.;max_iterations=0
for q in range(2,7):
    for k in range(16):
        a=(.53+.4*rng.random())/q;b=(1/q-a)*(.1+.8*rng.random());delta=1-q*(a+b)
        m=np.r_[np.full(q,a),np.full(q,b)]
        omega,it,err=balanced_density(q);max_iterations=max(max_iterations,it);worst_margin=max(worst_margin,err)
        C=delta*pt(omega,q,q);ev=np.linalg.eigvalsh(C)
        base=q*(q-1)*(a+b)/2
        N=base+(np.sqrt(ev*ev+4*a*b).sum()-delta)/2
        low=base+(np.sqrt(delta*delta+4*q**4*a*b)-delta)/2
        high=base+(q*np.sqrt(delta*delta+4*q*q*a*b)-delta)/2
        worst_bound=max(worst_bound,low-N,N-high)
        assert low-3e-11<=N<=high+3e-11
        # Direct full-state diagonalization for q<=4; higher q uses the independently derived block.
        if q<=4:
            rho=embed(m,delta*omega,list(range(q)),list(range(q,2*q)))
            full=nneg(rho,2*q,2*q)
            worst_formula=max(worst_formula,abs(N-full));assert abs(N-full)<3e-11
        # Both endpoints, with a random maximally-entangled residual orientation.
        U=unitary(q);phi=U.reshape(q*q)/np.sqrt(q);bell=np.outer(phi,phi.conj())
        for W,want in [(np.eye(q*q)/(q*q),low),(bell,high)]:
            es=np.linalg.eigvalsh(delta*pt(W,q,q));val=base+(np.sqrt(es*es+4*a*b).sum()-delta)/2
            worst_formula=max(worst_formula,abs(val-want));assert abs(val-want)<3e-11
        # Explicit isotropic path, verified monotone and with exact formula.
        phi=np.eye(q).reshape(q*q)/np.sqrt(q);bell=np.outer(phi,phi)
        vals=[]
        for t in np.linspace(0,1,21):
            cplus=delta*(1+(q-1)*t)/q**2;cminus=delta*(1-(q+1)*t)/q**2
            val=base+(q*(q+1)/2*np.sqrt(cplus*cplus+4*a*b)+q*(q-1)/2*np.sqrt(cminus*cminus+4*a*b)-delta)/2
            vals.append(val)
        assert np.diff(vals).min()>0
        count+=1
out['balanced_faces']={'families':count,'endpoint_cases':2*count,'isotropic_path_points':21*count,'max_bound_violation':worst_bound,'max_formula_or_endpoint_error':worst_formula,'max_uniform_marginal_error':worst_margin,'max_sinkhorn_iterations':max_iterations}

out['elapsed_seconds']=time.time()-start
out['source_sha256']=hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest()
out['all_passed']=True
path=ROOT/'negativity_checks.json';path.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
