"""Reproducible numerical falsification tests for the FEF refinements.

Numerical tests are diagnostics, not mathematical certificates. Exact symbolic
checks and the written proofs are separate. No optimizer is trusted as a proof.
"""
import argparse, json, pathlib
import numpy as np

ROOT=pathlib.Path(__file__).resolve().parent
P=np.array([[[0,1],[1,0]],[[0,-1j],[1j,0]],[[1,0],[0,-1]]],complex)
I=np.eye(2,dtype=complex)
A=np.array([np.kron(p,I) for p in P]); B=np.array([np.kron(I,p) for p in P])
TT=np.array([[np.kron(p,q) for q in P] for p in P])
MAGIC=np.array([[1,1j,0,0],[0,0,1j,1],[0,0,1j,-1],[1,-1j,0,0]],complex)/np.sqrt(2)

def partials(rho,d):
    x=rho.reshape(d,d,d,d)
    return np.einsum('ijkj->ik',x),np.einsum('ijil->jl',x)

def bloch(rho):
    return (np.einsum('ab,iba->i',rho,A).real,
            np.einsum('ab,iba->i',rho,B).real,
            np.einsum('ab,ijba->ij',rho,TT).real)

def fef(rho):
    _,_,T=bloch(rho);s=np.linalg.svd(T,compute_uv=False)
    return (1+s[0]+s[1]-np.sign(np.linalg.det(T))*s[2])/4

def canonical(rho):
    _,rb=partials(rho,2)
    vals,vec=np.linalg.eigh(rb)
    if vals[0]<1e-12:raise ValueError('rank-deficient or ill-conditioned Bob marginal')
    h=(vec*(1/np.sqrt(2*vals)))@vec.conj().T
    filt=np.kron(I,h)
    return filt@rho@filt.conj().T

def envelope(c,b):
    return (np.sqrt(1+b)+np.sqrt(max(0,1-c))*np.sqrt(max(0,1-b)))**2/4

def sharp_state(c,b):
    v=np.array([np.sqrt(1+b),0,0,np.sqrt((1-c)*(1-b))])
    out=np.outer(v,v)/2
    out[1,1]+=c*(1-b)/2
    return out.astype(complex)

def random_state(rng,d,rank):
    z=rng.normal(size=(d*d,rank))+1j*rng.normal(size=(d*d,rank))
    out=z@z.conj().T
    return out/np.trace(out)

def check_qubits(rng,n):
    worst={k:0.0 for k in ['joint_violation','milne_violation','ellipsoid_violation',
        'magic_svd_difference','centre_difference','quartic_residual','stability_violation']}
    min_slack=1.; skipped=0; worst_state=None
    for j in range(n):
        rho=random_state(rng,2,j%4+1)
        try:sigma=canonical(rho)
        except ValueError:skipped+=1;continue
        a,bv,T=bloch(rho); b=float(np.linalg.norm(bv))
        cv,_,S=bloch(sigma);c=float(np.linalg.norm(cv));Q=S@S.T
        f=fef(rho);F=envelope(c,b)
        worst['joint_violation']=max(worst['joint_violation'],f-F)
        worst['milne_violation']=max(worst['milne_violation'],f-1+c/2)
        worst['ellipsoid_violation']=max(worst['ellipsoid_violation'],f-np.linalg.eigvalsh(sigma)[-1])
        worst['magic_svd_difference']=max(worst['magic_svd_difference'],abs(f-np.linalg.eigvalsh((MAGIC.conj().T@rho@MAGIC).real)[-1]))
        worst['centre_difference']=max(worst['centre_difference'],np.linalg.norm(cv-(a-T@bv)/(1-b*b)))
        r=c*c+np.trace(Q);k=cv@Q@cv;d=np.linalg.det(S)
        z=4*np.linalg.eigvalsh(sigma)-1
        poly=z**4-2*r*z**2+8*d*z+r*r-4*k-2*np.trace(Q)**2+2*np.trace(Q@Q)
        worst['quartic_residual']=max(worst['quartic_residual'],max(abs(poly)))
        worst['stability_violation']=max(worst['stability_violation'],((2-c)*b-c)**2-8*(2-c)*(1-c/2-f))
        if F-f<min_slack:min_slack=F-f;worst_state={'c':c,'b':b,'f':f,'F':F,'rank':j%4+1}
    return {'count':n,'skipped':skipped,'maxima':worst,'minimum_joint_slack':min_slack,'closest_random_state':worst_state}

def check_sharp_family(rng,n):
    worst={k:0. for k in ['centre_error','bob_error','fef_error','nonpositivity','trace_error']}
    samples=[(0.,0.),(1.,0.),(0.,.8),(1.,.8),(.6,3/7),(.9,.99)]
    samples += [(float(rng.random()),float(rng.random())) for _ in range(n)]
    for c,b in samples:
        rho=sharp_state(c,b)
        cv,_,_=bloch(canonical(rho));_,bv,_=bloch(rho)
        worst['centre_error']=max(worst['centre_error'],abs(np.linalg.norm(cv)-c))
        worst['bob_error']=max(worst['bob_error'],abs(np.linalg.norm(bv)-b))
        worst['fef_error']=max(worst['fef_error'],abs(fef(rho)-envelope(c,b)))
        worst['nonpositivity']=max(worst['nonpositivity'],-min(np.linalg.eigvalsh(rho)))
        worst['trace_error']=max(worst['trace_error'],abs(np.trace(rho)-1))
    # The pure-Bob stratum has a different exact formula.
    singular=[]
    for c in [0.,.2,.6,1.]:
        rho=np.kron(np.diag([(1+c)/2,(1-c)/2]),np.diag([1.,0.]))
        singular.append({'c':c,'f':fef(rho),'exact':(1+c)/4})
    return {'count':len(samples),'maxima':worst,'singular_bob_tests':singular}

def coherent_min(alpha,beta,p):
    d=len(alpha);m=np.minimum(alpha,beta);u=alpha-m;v=beta-m;delta=float(u.sum())
    w=np.zeros(d*d)
    w[np.arange(d)*(d+1)]=np.sqrt(m)
    rho=np.outer(w,w)
    if delta>1e-14:rho+=np.diag((u[:,None]*v[None,:]/delta).ravel())
    x=np.zeros(d*d);x[np.arange(d)*(d+1)]=np.sqrt(p)
    return rho,x,float(np.dot(np.sqrt(p),np.sqrt(m))**2)

def check_general(rng,n):
    output=[]
    for d in [2,3,4,5,6]:
        worst=0.;sharp_err=0.;marginal_err=0.;pos_err=0.
        for j in range(n):
            rho=random_state(rng,d,[1,2,d,d*d][j%4])
            ra,rb=partials(rho,d)
            alpha=np.maximum(0,np.linalg.eigvalsh(ra)[::-1]);beta=np.maximum(0,np.linalg.eigvalsh(rb)[::-1])
            x=rng.normal(size=d*d)+1j*rng.normal(size=d*d);x/=np.linalg.norm(x)
            p=np.linalg.svd(x.reshape(d,d),compute_uv=False)**2
            cap=float(np.dot(np.sqrt(p),np.sqrt(np.minimum(alpha,beta)))**2)
            t=float(np.vdot(x,rho@x).real);worst=max(worst,t-cap)
            alpha=np.sort(rng.dirichlet(np.ones(d)))[::-1];beta=np.sort(rng.dirichlet(np.ones(d)))[::-1];p=np.sort(rng.dirichlet(np.ones(d)))[::-1]
            sigma,y,F=coherent_min(alpha,beta,p)
            a2,b2=partials(sigma,d)
            sharp_err=max(sharp_err,abs(y@sigma@y-F))
            marginal_err=max(marginal_err,np.max(abs(a2-np.diag(alpha))),np.max(abs(b2-np.diag(beta))))
            pos_err=max(pos_err,-min(np.linalg.eigvalsh(sigma)))
        output.append({'d':d,'random_tests':n,'sharpness_tests':n,'max_violation':worst,'max_sharpness_error':sharp_err,'max_marginal_error':marginal_err,'max_nonpositivity':pos_err})
    return output

def exact_examples():
    c=.6;b=3/7;rho=sharp_state(c,b)
    sigma=(np.eye(4)+.6*A[2]+.4*TT[0,0]-.4*TT[1,1]+.2*TT[2,2])/4
    K=np.kron(I,np.diag([1,.5]));filtered=K@sigma@K;success=float(np.trace(filtered).real);filtered/=success
    return {'canonical_bound_misuse_counterexample':{'c':c,'b':b,'actual_f':fef(rho),'canonical_bound':envelope(c,0)},
      'shape_refinement':{'canonical_spectrum':np.linalg.eigvalsh(sigma).tolist(),'c':.6,'centre_bound':.7,'ellipsoid_bound':.55,'achieved_f':fef(filtered),'filter_success':success},
      'higher_d_spectral_example':{'alpha':[.6,.3,.1],'beta':[.5,.4,.1],
          'fef_bound':float((np.sqrt(.5)+np.sqrt(.3)+np.sqrt(.1))**2/3),
          'marginal_A_only_bound':float((np.sqrt(.6)+np.sqrt(.3)+np.sqrt(.1))**2/3),
          'marginal_B_only_bound':float((np.sqrt(.5)+np.sqrt(.4)+np.sqrt(.1))**2/3)}}

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--qubits',type=int,default=20000);ap.add_argument('--general',type=int,default=600);ap.add_argument('--sharp',type=int,default=3000);ap.add_argument('--output',default=str(ROOT/'verification_results.json'));args=ap.parse_args()
    rng=np.random.default_rng(20261103)
    result={'seed':20261103,'scope':'Numerical falsification tests, not proofs',
      'qubits':check_qubits(rng,args.qubits),'sharp_family':check_sharp_family(rng,args.sharp),
      'general_spectral_overlap':check_general(rng,args.general),'examples':exact_examples()}
    for key,val in result['qubits']['maxima'].items():assert val<2e-7,(key,val)
    for row in result['general_spectral_overlap']:assert row['max_violation']<1e-10,row
    assert result['sharp_family']['maxima']['fef_error']<1e-10
    with open(args.output,'w') as f:json.dump(result,f,indent=2)
    print(json.dumps(result,indent=2))
