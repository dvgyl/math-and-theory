"""Independent check of unilateral CHSH spectral candidates.

This script uses direct complex 4x4 density-matrix filtering for the comparison
optimizer. The spectral code uses a whitened state and real 3x3 matrices.
Numerical agreement is evidence, not a proof of global optimality.
"""
import json
from pathlib import Path
import numpy as np
from scipy.optimize import minimize, brentq
from scipy.linalg import null_space

S = np.array([[[0,1],[1,0]], [[0,-1j],[1j,0]], [[1,0],[0,-1]]], complex)
I = np.eye(2, dtype=complex)
PAULI2 = np.array([[np.kron(s,t) for t in S] for s in S])

def partial_a(rho):
    return np.trace(rho.reshape(2,2,2,2), axis1=1, axis2=3)

def canonical(rho):
    e,V=np.linalg.eigh(partial_a(rho))
    F=(V*(1/np.sqrt(2*e)))@V.conj().T
    FF=np.kron(F,I)
    out=FF@rho@FF.conj().T
    return out/np.trace(out)

def bloch(rho):
    b=np.array([np.trace(rho@np.kron(I,s)).real for s in S])
    T=np.einsum('ab,ijba->ij',rho,PAULI2).real
    return b,T

def filter_direct(rho,u):
    r=np.linalg.norm(u)
    if r > 1+1e-9:
        return None
    r=min(r,1.)
    if r<1e-13:
        F=I
    else:
        sp,sm=np.sqrt(1+r),np.sqrt(1-r)
        F=(sp+sm)/2*I+(sp-sm)/(2*np.linalg.norm(u))*np.einsum('i,ijk->jk',u,S)
    FF=np.kron(F,I)
    out=FF@rho@FF.conj().T
    out=out/np.trace(out)
    T=np.einsum('ab,ijba->ij',out,PAULI2).real
    sv=np.linalg.svd(T,compute_uv=False)
    return float(sv[0]**2+sv[1]**2)

def cross(d):
    x,y,z=d
    return np.array([[0,-z,y],[z,0,-x],[-y,x,0]])

def boundary(A,d,b2):
    a,V=np.linalg.eigh(A); g=V.T@d; m=a[-1]
    top=np.abs(a-m)<1e-10
    low=~top
    if np.linalg.norm(g[top])<1e-10:
        w=np.zeros(3)
        w[low]=g[low]/(m-a[low])
        if np.dot(w,w)<=1+1e-10:
            w[np.flatnonzero(top)[0]]=np.sqrt(max(0,1-np.dot(w,w)))
            return b2+m+np.dot(g[low],w[low]), V@w
    def sec(lam): return np.sum((g/(lam-a))**2)-1
    lo=np.nextafter(m,np.inf)
    hi=m+1+np.linalg.norm(d)
    lam=brentq(sec,lo,hi,xtol=1e-14)
    w=g/(lam-a)
    w=w/np.linalg.norm(w)
    return b2+np.dot(w*a,w)+2*np.dot(g,w),V@w

def spectral(rho):
    b,T=bloch(rho); A=T@T.T; d=T@b; b2=b@b
    K=A-b2*np.eye(3); C=cross(d)
    bd,u=boundary(A,d,b2)
    best=(bd,u,'boundary')
    if min(abs(np.linalg.eigvalsh(K)))<1e-9:
        return None
    M=A+C@np.linalg.solve(K,C)
    mus,ns=np.linalg.eigh(M)
    for mu,n in zip(mus,ns.T):
        v=-np.linalg.solve(K,C@n)
        if abs(n@v)>1e-7 or np.linalg.norm(v)>=1-1e-9:
            continue
        u=-np.cross(n,v)
        val=np.trace(A)-mu
        assert abs(val-filter_direct(rho,u))<1e-7 or filter_direct(rho,u)>val-1e-7
        if val>best[0]: best=(val,u,'interior')
    return best

def eigengroups(vals,vecs,tol=1e-8):
    used=np.zeros(len(vals),bool)
    for i,val in enumerate(vals):
        if used[i]: continue
        mask=abs(vals-val)<tol
        used |= mask
        yield float(val),vecs[:,mask]

def spectral_all(rho,tol=1e-8):
    """Singular-safe spectral candidates, including the exceptional mu=|b|^2."""
    b,T=bloch(rho); A=T@T.T; d=T@b; q=b@b
    K=A-q*np.eye(3); C=cross(d)
    bd,u=boundary(A,d,q)
    best=(bd,u,'boundary')
    ke,kv=np.linalg.eigh(K)
    zero=abs(ke)<tol
    Z=kv[:,zero]
    ki=np.zeros(3);ki[~zero]=1/ke[~zero]
    Kplus=(kv*ki)@kv.T
    L=C@Z
    N=null_space(L.T,rcond=tol) if L.shape[1] else np.eye(3)
    B=A+C@Kplus@C
    vals,vecs=np.linalg.eigh(N.T@B@N)
    for mu,Q0 in eigengroups(vals,vecs,tol):
        if abs(mu-q)<tol: continue
        Q=N@Q0
        V=-Kplus@C@Q
        if Z.shape[1]:
            V+=Z@np.linalg.pinv(L,rcond=tol)@(B-mu*np.eye(3))@Q
        ve,vv=np.linalg.eigh(V.T@V)
        if ve[0]>=1-tol: continue
        n=Q@vv[:,0];v=V@vv[:,0]
        assert abs(n@v)<1e-6,(mu,q,n@v)
        assert np.linalg.norm(K@v+C@n)<1e-6
        assert np.linalg.norm(A@n-C@v-mu*n)<1e-6
        u=-np.cross(n,v);val=np.trace(A)-mu
        if val>best[0]: best=(float(val),u,'interior')
    H=K+1j*C
    he,hv=np.linalg.eigh(H)
    U=hv[:,abs(he)<tol]
    if U.shape[1] and np.linalg.norm(U.T@U)>tol:
        choices=[U[:,i] for i in range(U.shape[1])]
        choices += [U[:,i]+U[:,j] for i in range(U.shape[1]) for j in range(i)]
        z=max(choices,key=lambda z:abs(z@z))
        if abs(z@z)>tol:
            z=z*np.exp(-.5j*np.angle(z@z))
            z=z/np.linalg.norm(z.real)
            n,v=z.real,z.imag
            assert abs(n@v)<1e-6
            assert np.linalg.norm(v)<1
            u=-np.cross(n,v);val=np.trace(A)-q
            if val>best[0]:best=(float(val),u,'exceptional')
    return best

def density(b,T):
    return (np.kron(I,I)+sum(b[j]*np.kron(I,S[j]) for j in range(3))+
            sum(T[i,j]*PAULI2[i,j] for i in range(3) for j in range(3)))/4

def swap(rho):
    return rho.reshape(2,2,2,2).transpose(1,0,3,2).reshape(4,4)

def additional_checks():
    rng=np.random.default_rng(130621)
    records=[]
    # Original, noncanonical states, both parties.
    for rank in [4,3,2,1]:
        for i in range(10):
            X=rng.normal(size=(4,rank))+1j*rng.normal(size=(4,rank))
            rho=X@X.conj().T;rho/=np.trace(rho)
            for side,raw in [('Alice',rho),('Bob',swap(rho))]:
                can=canonical(raw)
                spec=spectral_all(can)
                num=optimize_direct(raw,rng,12)
                records.append({'type':'noncanonical','rank':rank,'i':i,'side':side,
                                'spectral':spec[0],'direct':num[0],'gap':spec[0]-num[0]})
    # Physical canonical states with exact singular K, ranks K=0,1,2.
    for diag in [[.3,-.2,.1],[.2,-.2,.1],[.2,-.2,.2]]:
        qroot=.1 if diag[0]==.3 else .2
        for i in range(10):
            direction=rng.normal(size=3);direction/=np.linalg.norm(direction)
            b=qroot*direction;T=np.diag(diag);rho=density(b,T)
            assert min(np.linalg.eigvalsh(rho))>-1e-12
            spec=spectral_all(rho);num=optimize_direct(rho,rng,15)
            records.append({'type':'singular_K','T':diag,'i':i,'spectral':spec[0],
                            'direct':num[0],'gap':spec[0]-num[0]})
    q=(15-np.sqrt(105))/40
    rho=density(np.array([0,0,np.sqrt(q)]),np.diag([np.sqrt(.3),-.5,np.sqrt(.2)]))
    spec=spectral_all(rho);num=optimize_direct(rho,rng,30)
    records.append({'type':'exceptional_exact','spectral':spec[0],'direct':num[0],
                    'expected':.75-q,'branch':spec[2],'gap':spec[0]-num[0]})
    rho=np.array([[20,0,0,14],[0,0,0,0],[0,0,7,0],[14,0,0,13]],complex)/40
    for side,raw,expected in [('Alice',rho,79/75),('Bob',swap(rho),292/247)]:
        spec=spectral_all(canonical(raw));num=optimize_direct(raw,rng,25)
        records.append({'type':'activation_canonical','side':side,'spectral':spec[0],
                        'direct':num[0],'expected':expected,'gap':spec[0]-num[0]})
    rho=np.array([[441,0,0,56],[0,49,0,0],[0,0,1,0],[56,0,0,9]],complex)/500
    for side,raw,expected in [('Alice',rho,32/25),('Bob',swap(rho),(220/221)**2)]:
        spec=spectral_all(canonical(raw));num=optimize_direct(raw,rng,25)
        records.append({'type':'one_side_only','side':side,'spectral':spec[0],
                        'direct':num[0],'expected':expected,'gap':spec[0]-num[0]})
    summary={'seed':130621,'tested':len(records),
             'max_absolute_gap':max(abs(r['gap']) for r in records),
             'max_gap':max(r['gap'] for r in records),'min_gap':min(r['gap'] for r in records),
             'records':records}
    Path(__file__).with_name('additional_results.json').write_text(json.dumps(summary,indent=2))
    print(json.dumps({k:v for k,v in summary.items() if k!='records'},indent=2))

def optimize_direct(rho,rng,starts=8):
    def f(u):
        r=np.linalg.norm(u)
        if r>1: u=u/r
        return -filter_direct(rho,u)
    cons={'type':'ineq','fun':lambda u:1-u@u}
    best=(-1,None)
    for j in range(starts):
        u=np.zeros(3) if j==0 else rng.normal(size=3)
        if j: u=u/np.linalg.norm(u)*rng.uniform(0,.99)
        opt=minimize(f,u,constraints=cons,method='SLSQP',options={'maxiter':200,'ftol':1e-11})
        u=opt.x
        if np.linalg.norm(u)>1: u=u/np.linalg.norm(u)
        val=filter_direct(rho,u)
        if val>best[0]: best=(val,u)
    return best

def main():
    rng=np.random.default_rng(240603945)
    records=[]; skipped=0; maxgap=0.; max_under=0.
    for rank in [4,3,2,1]:
        for i in range(40):
            X=rng.normal(size=(4,rank))+1j*rng.normal(size=(4,rank))
            rho=X@X.conj().T;rho=rho/np.trace(rho)
            rho=canonical(rho)
            spec=spectral(rho)
            if spec is None: skipped+=1; continue
            num=optimize_direct(rho,rng)
            gap=spec[0]-num[0]
            maxgap=max(maxgap,gap);max_under=min(max_under,gap)
            if gap>1e-6:
                num=optimize_direct(rho,rng,starts=35)
                gap=spec[0]-num[0]
            records.append({'rank':rank,'i':i,'spectral':spec[0],'direct':num[0],'gap':gap,'branch':spec[2]})
            if abs(gap)>1e-5:
                print('MISMATCH',records[-1],flush=True)
    summary={'seed':240603945,'attempted':160,'tested':len(records),'singular_K_skipped':skipped,
             'max_absolute_gap':max(abs(r['gap']) for r in records),'max_gap':max(r['gap'] for r in records),
             'min_gap':min(r['gap'] for r in records),'records':records}
    path=Path(__file__).with_name('check_results.json');path.write_text(json.dumps(summary,indent=2))
    print(json.dumps({k:v for k,v in summary.items() if k!='records'},indent=2))
if __name__=='__main__':
    import sys
    additional_checks() if '--additional' in sys.argv else main()
