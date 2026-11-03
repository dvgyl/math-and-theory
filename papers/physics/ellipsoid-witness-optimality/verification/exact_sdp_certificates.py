#!/usr/bin/env python3
"""Exact primal/dual and containment certificates using all principal minors.

No solver and no floating-point arithmetic enter these certificates.
"""
from pathlib import Path
from itertools import combinations
import json
import sympy as s

R=s.Rational; I=s.eye(2)
sig=[s.Matrix([[0,1],[1,0]]),s.Matrix([[0,-s.I],[s.I,0]]),s.diag(1,-1)]

def projector(v):
    return v*v.conjugate().T/(v.conjugate().T*v)[0]
Phi=projector(s.Matrix([1,0,0,1]))
Minus=projector(s.Matrix([0,1,-1,0]))
Plus=projector(s.Matrix([0,1,1,0]))

def canonical(c,A):
    out=s.eye(4)
    for i in range(3):
        out+=c[i]*s.kronecker_product(sig[i],I)
        for j in range(3):out+=A[i,j]*s.kronecker_product(sig[i],sig[j])
    return out/4

def image(Q,c,A,transpose=True):
    out=s.zeros(4)
    for a in range(2):
        for d in range(2):
            E=s.zeros(2);E[a,d]=1
            scalar=s.trace(E)/2
            coords=s.Matrix([s.trace(P*E)/2 for P in sig])
            L=scalar*I
            for i in range(3):L+=(scalar*c[i]+(A*coords)[i])*sig[i]
            block=Q[2*a:2*a+2,2*d:2*d+2]
            if transpose:block=block.T
            out+=s.kronecker_product(L,block)
    return s.simplify(out)

def adjoint(X,c,A):
    out=s.zeros(4)
    for P in [I,*sig]:
        for Q in [I,*sig]:
            B=s.kronecker_product(P,Q)
            out+=s.trace(image(B,c,A).conjugate().T*X)/4*B
    return s.simplify(out)

def exact_psd(A):
    if A != A.conjugate().T:raise AssertionError('Matrix is not Hermitian')
    minors=[]
    for k in range(1,5):
        for ix in combinations(range(4),k):
            d=s.simplify(A.extract(ix,ix).det())
            if not (d.is_real and d>=0):raise AssertionError(('Negative or undecided minor',ix,d))
            minors.append({'indices':ix,'determinant':str(d)})
    return minors

def main():
    z=s.zeros(3,1); results={}
    cases=[
      ('class_d_original',canonical(z,s.diag(1,1,-R(1,2))),s.diag(1,1,R(1,2)),R(1,3),R(8,3)),
      ('class_d_interior',canonical(z,s.diag(R(3,4),R(3,4),-R(1,4))),s.diag(R(3,4),R(3,4),R(1,4)),R(1,3),R(16,3)),
      ('class_c_spheres',canonical(z,s.diag(R(1,2),R(1,2),R(1,2))),s.diag(R(3,4),R(3,4),R(3,4)),R(2,5),R(16,5)),
      ('class_d_planar',canonical(z,s.diag(R(9,16),0,R(9,16))),s.diag(R(3,4),0,R(3,4)),R(1,4),8),
      ('refinement_without_containment',canonical(z,s.diag(1,1,-R(4,5))),s.diag(1,1,R(1,2)),R(2,15),R(8,3))]
    for name,W,A,alpha,scale in cases:
        Q=alpha*Phi;X=scale*Minus
        residual=W-image(Q,z,A);slack=s.eye(4)+adjoint(X,z,A)
        checks={key:exact_psd(mat) for key,mat in
                [('source',Q),('residual',residual),('dual',X),('dual_slack',slack)]}
        primal=s.trace(Q);dual=-s.trace(X*W)
        assert s.simplify(primal-alpha)==0 and s.simplify(primal-dual)==0
        assert s.simplify(s.trace(slack*Q))==0 and s.simplify(s.trace(X*residual))==0
        results[name]={'exact_alpha':str(alpha),'primal_objective':str(primal),
                       'dual_objective':str(dual),'principal_minors':checks,
                       'source_rank':Q.rank(),'residual_rank':residual.rank()}
    A=s.diag(1,1,R(1,2));W=canonical(z,s.diag(1,1,-R(1,2)))
    assert image(Plus,z,A,False)==W
    results['class_d_containment_source']={'P':'P_PsiPlus','Q':'0','identity_verified':True,
                                         'source_principal_minors':exact_psd(Plus)}
    # A planar containment certificate before optimization, and its transpose collapse.
    A=s.diag(R(3,4),0,R(3,4));P=s.eye(4)/16;Q=R(3,4)*Phi
    W=canonical(z,s.diag(R(9,16),0,R(9,16)))
    assert image(P,z,A,False)+image(Q,z,A)==W
    assert image(P.T+Q,z,A)==W
    results['planar_containment_source']={'identity_verified':True,
                                         'collapsed_source_rank':(P.T+Q).rank(),
                                         'P_principal_minors':exact_psd(P),
                                         'Q_principal_minors':exact_psd(Q)}
    out={'arithmetic':'exact SymPy rational/complex arithmetic',
         'psd_method':'Hermiticity and every principal minor nonnegative',
         'optimization_certificates':5,'containment_certificates':2,'failed':0,
         'examples':results}
    target=Path(__file__).with_name('exact_sdp_certificates.json')
    target.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k!='examples'},indent=2))

if __name__=='__main__':main()
