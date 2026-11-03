#!/usr/bin/env python3
"""Falsification and exact algebra checks for the sharp(c,trQ) envelope."""
from pathlib import Path
import json
import numpy as np
import sympy as sp
from scipy.optimize import minimize

HERE=Path(__file__).resolve().parent
rng=np.random.default_rng(2026110305)

def spectra(c,l):
    h=c/2
    if l<=min((2+3*c)/8,.5)+1e-13:
        return np.array([l,.5-l+h,l-h,.5-l]),1
    if c<=2/3 and l<=1-3*c/4+1e-13:
        r=(1-l)/3
        return np.array([l,r+h/2,r,r-h/2]),2
    return np.array([l,h,1-l-h,0.]),3

def sharp(c,l):
    ev,phase=spectra(c,l);_,u,v,w=ev;h=c/2
    a=(l+v+h)/2;d=(l+v-h)/2
    z=np.sqrt(max(0,(l-v)**2-h*h))/2
    rho=np.array([[a,0,0,z],[0,u,0,0],[0,0,w,0],[z,0,0,d]])
    return rho,ev,phase

def H(c,q):
    if q<=min(c*c/4,(1-c)**2)+1e-12:
        return (1+c+np.sqrt(max(0,q)))/4
    if c<=2/3 and q<=3-6*c+2.5*c*c+1e-12:
        return (1+np.sqrt(max(0,3*q+1.5*c*c)))/4
    return (2-c+np.sqrt(max(0,2*q+4*c-2-c*c)))/4

def partials(r):
    t=r.reshape(2,2,2,2)
    return np.einsum('abcb->ac',t),np.einsum('abad->bd',t)

def canonical(r):
    _,b=partials(r);ev,u=np.linalg.eigh(b)
    K=(u/np.sqrt(2*ev))@u.conj().T
    F=np.kron(np.eye(2),K)
    return F@r@F

def parameters(s):
    a,b=partials(s)
    c=float(np.linalg.eigvalsh(a)[1]-np.linalg.eigvalsh(a)[0])
    p=float(np.trace(s@s).real);q=4*p-1-c*c
    return c,q,p

def exact():
    c,l,u,v=sp.symbols('c l u v',real=True)
    w=1-l-u-v;h=c/2;r=(1-l)/3
    z1=[sp.Rational(1,2)-l+h,l-h,sp.Rational(1,2)-l]
    z2=[r+h/2,r,r-h/2];z3=[h,1-l-h,0]
    identities={}
    for idx,z in enumerate([z1,z2,z3],1):
        ds=[u-z[0],v-z[1],w-z[2]]
        difference=u*u+v*v+w*w-sum(t*t for t in z)
        if idx==1:
            d=2*l-h-sp.Rational(1,2)
            linear=d*(2*ds[0]+ds[1])+(h-2*d)*ds[0]
        elif idx==2:linear=h/2*(ds[0]-ds[2])
        else:
            v0=1-l-h
            linear=(h-v0)*(ds[0]-ds[2])+(h-2*v0)*ds[2]
        identities[f'phase_{idx}_certificate']=sp.expand(difference-sum(t*t for t in ds)-2*linear)==0
    q=sp.symbols('q',nonnegative=True)
    bounds=[(1+c+sp.sqrt(q))/4,(1+sp.sqrt(3*q+3*c*c/2))/4,
            (2-c+sp.sqrt(2*q+4*c-2-c*c))/4]
    purities=[(1+c*c)/4+4*(l-(1+c)/4)**2,l*l+(1-l)**2/3+c*c/8,
              l*l+h*h+(1-l-h)**2]
    for idx,(bound,purity) in enumerate(zip(bounds,purities),1):
        identities[f'phase_{idx}_inverse']=sp.simplify(purity.subs(l,bound)-(1+c*c+q)/4)==0
    sample=sp.Matrix([[sp.Rational(1,2),0,0,sp.sqrt(3)/10],
                      [0,sp.Rational(3,10),0,0],[0,0,0,0],
                      [sp.sqrt(3)/10,0,0,sp.Rational(1,5)]])
    x=sp.symbols('x')
    expected=x*(x-sp.Rational(3,10))*(x-(7+sp.sqrt(21))/20)*(x-(7-sp.sqrt(21))/20)
    identities['sample_characteristic_polynomial']=sp.expand(sample.charpoly(x).as_expr()-expected)==0
    identities['sample_purity']=sp.trace(sample**2)==sp.Rational(11,25)
    assert all(identities.values()),identities
    return identities

def main():
    sharp_errors=dict(spectrum=0.,marginal=0.,envelope=0.,negativity=0.,shape_domain=0.)
    phases={1:0,2:0,3:0}
    for c in np.linspace(0,1,51):
        for l in np.linspace((1+c)/4,1-c/2,101):
            rho,ev,phase=sharp(c,l);a,b=partials(rho);cr,q,p=parameters(rho)
            sharp_errors['spectrum']=max(sharp_errors['spectrum'],np.max(np.abs(np.linalg.eigvalsh(rho)[::-1]-ev)))
            sharp_errors['marginal']=max(sharp_errors['marginal'],np.linalg.norm(a-np.diag([(1+c)/2,(1-c)/2])),np.linalg.norm(b-np.eye(2)/2))
            sharp_errors['envelope']=max(sharp_errors['envelope'],abs(H(c,q)-l))
            sharp_errors['negativity']=max(sharp_errors['negativity'],-float(np.linalg.eigvalsh(rho).min()))
            sharp_errors['shape_domain']=max(sharp_errors['shape_domain'],-q,q-(3-4*c+c*c))
            phases[phase]+=1
    random_cases=40000;maximum_excess=0.;bravyi_excess=0.
    for i in range(random_cases):
        rank=1+i%4
        g=rng.normal(size=(4,rank))+1j*rng.normal(size=(4,rank))
        rho=g@g.conj().T;rho/=np.trace(rho).real;s=canonical(rho)
        c,q,p=parameters(s);ev=np.linalg.eigvalsh(s)[::-1];l,u,v,w=ev
        maximum_excess=max(maximum_excess,l-H(c,q))
        bravyi_excess=max(bravyi_excess,v+w-(1-c)/2,c/2-(l-v),c/2-(u-w))
    # Independent constrained optimization of the three remaining eigenvalues.
    qp_error=0.;qp_bad=0;qp_cases=180
    for _ in range(qp_cases):
        c=rng.uniform(.001,.999);l=rng.uniform((1+c)/4,1-c/2)
        ev,_=spectra(c,l);h=c/2
        cons=[{'type':'eq','fun':lambda y:sum(y)-(1-l)},
              {'type':'ineq','fun':lambda y:np.array([l-y[0],y[0]-y[1],y[1]-y[2],y[2],
                   (1-c)/2-y[1]-y[2],l-y[1]-h,y[0]-y[2]-h])}]
        r=minimize(lambda y:float(y@y),ev[1:]+rng.normal(scale=.0005,size=3),constraints=cons,
                   method='SLSQP',options={'ftol':1e-13,'maxiter':300})
        if not r.success:qp_bad+=1
        qp_error=max(qp_error,abs(r.fun-float(ev[1:]@ev[1:])))
    result=dict(seed=2026110305,sharp_cases=51*101,sharp_errors=sharp_errors,
                sharp_phases=phases,random_cases=random_cases,maximum_envelope_excess=maximum_excess,
                maximum_bravyi_excess=bravyi_excess,qp_cases=qp_cases,qp_unsuccessful=qp_bad,
                qp_max_value_difference=qp_error,exact_identities=exact(),
                note='Theorems use exact certificates. Numeric tests diagnose implementation and search for counterexamples.')
    assert max(sharp_errors.values())<2e-7
    assert maximum_excess<2e-7
    assert qp_error<2e-8
    (HERE/'purity_envelope_results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
