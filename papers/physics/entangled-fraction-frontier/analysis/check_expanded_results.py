#!/usr/bin/env python3
"""Deterministic falsification checks for the expanded exact theorems.

These floating-point checks are diagnostics, not mathematical proofs. In d>2
the script checks the exhibited target and analytic cap, not a numerical global
optimization over maximally entangled targets.
"""
from pathlib import Path
import json, sys
import numpy as np

HERE = Path(__file__).resolve().parent
for candidate in [HERE, HERE.parent.parent/'analysis']:
    if (candidate/'verify_results.py').exists(): sys.path.insert(0,str(candidate));break
from verify_results import partials, fef, sharp_state, envelope, random_state, coherent_min

def outer(x): return np.outer(x,x.conj())

def dual(a,b,p,eta=0.):
    d=len(a);m=np.minimum(a,b);S=np.sqrt(p*(m+eta)).sum()
    ell=S*np.sqrt(p/(m+eta))
    h=np.where(a<b,ell,np.where(a>b,0.,ell/2));k=ell-h
    x=np.zeros(d*d);x[np.arange(d)*(d+1)]=np.sqrt(p)
    Z=np.diag((h[:,None]+k[None,:]).ravel())-outer(x)
    return Z,ell,float(a@h+b@k)

def diagonal_tests(rng,n=2500):
    out={'cases':n,'max_population_violation':0.,'max_dual_nonpositivity':0.,
         'max_dual_value_error':0.,'max_kernel_dimension_error':0,
         'max_gap_identity_error':0.,'max_support_stability_violation':0.,
         'max_support_projection_distance_violation':0.}
    for it in range(n):
        d=2+it%5
        a=rng.dirichlet(np.ones(d)*2);b=rng.dirichlet(np.ones(d)*2)
        if it%17==0:b=a.copy()
        p=rng.dirichlet(np.ones(d)*2)
        rho0,x,cap=coherent_min(a,b,p)
        phase=rng.uniform(0,2*np.pi,d)
        U=np.kron(np.diag(np.exp(1j*phase)),np.eye(d))
        rho1=U@rho0@U.conj().T
        t=float(rng.random());rho=t*rho1+(1-t)*np.diag(np.outer(a,b).ravel())
        overlap=float(np.vdot(x,rho@x).real)
        out['max_population_violation']=max(out['max_population_violation'],overlap-cap)
        Z,ell,value=dual(a,b,p)
        vals,vec=np.linalg.eigh(Z)
        out['max_dual_nonpositivity']=max(out['max_dual_nonpositivity'],-float(vals.min()))
        out['max_dual_value_error']=max(out['max_dual_value_error'],abs(value-cap))
        plus=int(np.sum(a>b));minus=int(np.sum(b>a));zero=vals<1e-9
        out['max_kernel_dimension_error']=max(out['max_kernel_dimension_error'],abs(int(zero.sum())-1-plus*minus))
        P=vec[:,zero]@vec[:,zero].conj().T
        outside=float(np.trace((np.eye(d*d)-P)@rho).real)
        gap=cap-overlap
        out['max_gap_identity_error']=max(out['max_gap_identity_error'],abs(np.trace(Z@rho).real-gap))
        out['max_support_stability_violation']=max(out['max_support_stability_violation'],outside-2*gap/ell.min())
        projected=P@rho@P;prob=float(np.trace(projected).real)
        if prob>1e-10:
            distance=float(np.abs(np.linalg.eigvalsh(rho-projected/prob)).sum())
            out['max_support_projection_distance_violation']=max(out['max_support_projection_distance_violation'],distance-2*np.sqrt(max(0,outside)))
    return out

def population_random_tests(rng,n=4000):
    out={'cases':n,'max_violation':0.,'max_individual_cap_stability_violation':0.,'max_total_cap_stability_violation':0.}
    for k in range(n):
        d=2+k%5;rho=random_state(rng,d,1+k%(d*d))
        A,B=partials(rho,d);a=np.diag(A).real;b=np.diag(B).real
        p=rng.dirichlet(np.ones(d));x=np.zeros(d*d);x[np.arange(d)*(d+1)]=np.sqrt(p)
        t=float(np.vdot(x,rho@x).real);popcap=float(np.sqrt(p*np.minimum(a,b)).sum()**2)
        out['max_violation']=max(out['max_violation'],t-popcap)
        # General spectral-cap stability uses sorted Schmidt coefficients.
        alpha=np.maximum(0,np.linalg.eigvalsh(A)[::-1]);beta=np.maximum(0,np.linalg.eigvalsh(B)[::-1])
        ps=np.sort(p)[::-1];m=np.minimum(alpha,beta);S=float(np.sqrt(ps*m).sum())
        w=rho@x/np.sqrt(t);q=np.linalg.svd(w.reshape(d,d),compute_uv=False)**2
        eps=S*S-t
        individual=np.sqrt(ps)*S*(m-q)-2*np.sqrt(m)*eps
        total=float((m-q).sum()-2*np.sqrt(m.max())*eps/(S*np.sqrt(ps.min())))
        out['max_individual_cap_stability_violation']=max(out['max_individual_cap_stability_violation'],float(individual.max()))
        out['max_total_cap_stability_violation']=max(out['max_total_cap_stability_violation'],total)
    return out

def success_frontier(c,q):
    L=1-c/2
    return L if q<=L else (1+np.sqrt((1-c)*(2*q-1)))**2/(4*q)

def success_tests(rng,n=6000):
    out={'cases':n+12,'max_feasible_violation':0.,'max_attainment_error':0.,
         'max_kraus_excess':0.,'max_probability_error':0.}
    cases=[(c,q) for c in [0.,.6,1.] for q in [.2,.5,.8,1.]]
    cases.extend(zip(rng.random(n),rng.uniform(.0001,1,n)))
    for c,q in cases:
        L=1-c/2;b=min(c/(2-c),(1-q)/q)
        K=np.diag(np.sqrt([q*(1+b),q*(1-b)]))
        sigma=sharp_state(c,0);G=np.kron(np.eye(2),K)
        unnorm=G@sigma@G.T;prob=float(np.trace(unnorm).real);rho=unnorm/prob
        bound=success_frontier(c,q)
        out['max_attainment_error']=max(out['max_attainment_error'],abs(fef(rho)-bound))
        out['max_probability_error']=max(out['max_probability_error'],abs(prob-q))
        out['max_kraus_excess']=max(out['max_kraus_excess'],float(np.linalg.eigvalsh(K.T@K).max()-1))
        B=min(1.,(1-q)/q);br=float(rng.uniform(0,B)) if B>0 else 0.
        out['max_feasible_violation']=max(out['max_feasible_violation'],envelope(c,br)-bound)
    return out

def universal_embedding_tests(rng,n=300):
    out={'cases':n,'max_marginal_error':0.,'max_attainment_error':0.,'max_negative_eigenvalue':0.,
         'max_local_extraction_error':0.,'max_rank_error':0,'max_sorting_violation':0.}
    for it in range(n):
        r=2+it%2;s=2+(it//2)%2;d=r+s
        rank=1+it%(r*s)
        V0=rng.normal(size=(r*s,rank))+1j*rng.normal(size=(r*s,rank))
        omega=V0@V0.conj().T;omega/=np.trace(omega)
        tensor=omega.reshape(r,s,r,s)
        A=np.trace(tensor,axis1=1,axis2=3);B=np.trace(tensor,axis1=0,axis2=2)
        av,au=np.linalg.eigh(A);bv,bu=np.linalg.eigh(B)
        L=np.kron(au.conj().T,bu.conj().T);omega=L@omega@L.conj().T
        lam=np.arange(d,0,-1,dtype=float);lam/=lam.sum()
        gap=float(np.min(lam[:-1]-lam[1:]));delta=gap/(3+gap)
        m=(1-delta)*lam;a=m.copy();b=m.copy();a[:r]+=delta*av;b[r:]+=delta*bv
        V=np.zeros((d*d,r*s))
        for i in range(r):
            for j in range(s):V[i*d+r+j,i*s+j]=1.
        z=np.zeros(d*d);z[np.arange(d)*(d+1)]=np.sqrt(m)
        rho=outer(z)+delta*V@omega@V.T
        phi=np.zeros(d*d);phi[np.arange(d)*(d+1)]=1/np.sqrt(d)
        aa,bb=partials(rho,d);P=V@V.T
        out['max_marginal_error']=max(out['max_marginal_error'],float(abs(aa-np.diag(a)).max()),float(abs(bb-np.diag(b)).max()))
        out['max_attainment_error']=max(out['max_attainment_error'],abs(np.vdot(phi,rho@phi).real-np.sqrt(np.minimum(a,b)).sum()**2/d))
        out['max_negative_eigenvalue']=max(out['max_negative_eigenvalue'],-float(np.linalg.eigvalsh(rho).min()))
        out['max_local_extraction_error']=max(out['max_local_extraction_error'],float(abs(P@rho@P/delta-V@omega@V.T).max()))
        out['max_rank_error']=max(out['max_rank_error'],abs(int((np.linalg.eigvalsh(rho)>1e-10).sum())-rank-1))
        out['max_sorting_violation']=max(out['max_sorting_violation'],float(np.diff(a).max()),float(np.diff(b).max()))
    return out

def boundary_and_fourdimensional():
    a=np.array([.3,.2,.5,0]);b=np.array([.3,.2,0,.5]);p=np.array([.1,.2,.3,.4]);m=np.minimum(a,b)
    z=np.zeros(16);z[np.arange(4)*5]=np.sqrt(m)
    y=np.zeros(16,dtype=complex);y[2*4+3]=.5j
    R=np.zeros((16,16),complex);R[11,11]=.5
    rho=outer(z)+np.outer(z,y.conj())+np.outer(y,z)+R
    x=np.zeros(16);x[np.arange(4)*5]=np.sqrt(p);S=np.sqrt(p*m).sum()
    aa,bb=partials(rho,4)
    reg=[]
    for eta in [1e-2,1e-4,1e-6,1e-8,1e-10]:
        Z,ell,val=dual(a,b,p,eta)
        reg.append({'eta':eta,'dual_gap':float(val-S*S),'min_slack_eigenvalue':float(np.linalg.eigvalsh(Z).min()),'largest_multiplier':float(ell.max())})
    m4=np.array([16,9,4,1])/36;z4=np.zeros(16);z4[np.arange(4)*5]=np.sqrt(m4)
    V=np.zeros((16,4))
    for i in range(2):
        for j in range(2):V[(2*i)*4+2*j+1,2*i+j]=1
    phi2=np.array([1,0,0,1])/np.sqrt(2);phi4=np.zeros(16);phi4[np.arange(4)*5]=.5
    four=[]
    for name,omega in [('bell',outer(phi2)),('maximally_mixed',np.eye(4)/4)]:
        st=outer(z4)+V@omega@V.T/6;A,B=partials(st,4)
        four.append({'residual':name,'bell_overlap':float(phi4@st@phi4),'certified_spectral_cap':float(np.sqrt(np.minimum(np.linalg.eigvalsh(A)[::-1],np.linalg.eigvalsh(B)[::-1])).sum()**2/4),
                     'rank':int((np.linalg.eigvalsh(st)>1e-10).sum()),'alice':np.diag(A).real.tolist(),'bob':np.diag(B).real.tolist()})
    return {'boundary_marginal_error':float(max(abs(aa-np.diag(a)).max(),abs(bb-np.diag(b)).max())),
            'boundary_min_eigenvalue':float(np.linalg.eigvalsh(rho).min()),'boundary_overlap_error':float(abs(np.vdot(x,rho@x).real-S*S)),
            'boundary_cross_norm':float(np.linalg.norm(np.outer(z,y.conj())+np.outer(y,z))),
            'regularized_dual':reg,'fourdimensional':four}

def main():
    rng=np.random.default_rng(2026110303)
    result={'seed':2026110303,'scope':'Deterministic floating-point falsification diagnostics; not proofs',
            'fixed_marginal_duals':diagonal_tests(rng),
            'random_population_and_spectral_stability':population_random_tests(rng),
            'filter_success':success_tests(rng),'universal_embeddings':universal_embedding_tests(rng),
            'boundary_and_exact_families':boundary_and_fourdimensional()}
    for section in ['fixed_marginal_duals','random_population_and_spectral_stability','filter_success','universal_embeddings']:
        for k,v in result[section].items():
            if k.startswith('max_'):assert v<1e-8,(section,k,v)
    bd=result['boundary_and_exact_families'];assert bd['boundary_marginal_error']<1e-12;assert bd['boundary_min_eigenvalue']>-1e-12
    assert bd['boundary_overlap_error']<1e-12
    for row in bd['fourdimensional']:assert abs(row['bell_overlap']-25/36)<1e-12
    (HERE/'expanded_check_results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
