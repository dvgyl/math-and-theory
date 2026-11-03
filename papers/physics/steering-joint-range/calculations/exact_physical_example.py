#!/usr/bin/env python3
"""Check the report's explicit Kraus protocol in exact rational arithmetic."""
from pathlib import Path
import itertools,json
import sympy as s

R=s.Rational
pauli=[s.Matrix([[0,1],[1,0]]),s.Matrix([[0,-s.I],[s.I,0]]),s.diag(1,-1)]

def minors(A):
    out=[]
    for k in range(1,A.rows+1):
        for inds in itertools.combinations(range(A.rows),k):
            d=s.factor(A.extract(inds,inds).det())
            assert d.is_real and d>=0,(inds,d)
            out.append({'indices':list(inds),'determinant':str(d)})
    return out

def bloch(M):
    a=s.Matrix([s.trace(M*s.kronecker_product(P,s.eye(2))) for P in pauli])
    b=s.Matrix([s.trace(M*s.kronecker_product(s.eye(2),P)) for P in pauli])
    T=s.Matrix([[s.trace(M*s.kronecker_product(P,Q)) for Q in pauli] for P in pauli])
    return a,b,T

def main():
    sigma=s.Matrix([[25,0,0,15],[0,16,0,0],[0,0,0,0],[15,0,0,9]])/50
    G=s.diag(1,R(5,13)); J=s.kronecker_product(s.eye(2),G)
    unnormalized=J*sigma*J.conjugate().T
    p=s.trace(unnormalized); rho=unnormalized/p
    assert p==R(97,169)
    assert rho==s.Matrix([[169,0,0,39],[0,16,0,0],[0,0,0,0],[39,0,0,9]])/194
    a0,b0,S=bloch(sigma); a,b,T=bloch(rho)
    assert a0==s.Matrix([0,0,R(16,25)]) and b0==s.zeros(3,1)
    assert S==s.diag(R(3,5),-R(3,5),R(9,25))
    assert a==s.Matrix([0,0,R(88,97)]) and b==s.Matrix([0,0,R(72,97)])
    assert T==s.diag(R(39,97),-R(39,97),R(81,97))
    r=R(72,97); c=R(16,25); D=2-2*c-c*c
    tau=s.trace(S.T*S); value=s.trace(T.T*T)
    assert tau==R(531,625) and value==R(99,97)
    assert (a-T*b)/(1-(b.T*b)[0])==a0
    assert r==c*(1-c)/D
    assert value==1+(2-3*c)**2/D
    assert (1-r*r)*(3-4*c)+(c+(1-c)*r)**2==value
    assert p==D/(2-c-2*c*c) and D/(2*c*(1-c))==R(97,144)
    result={'status':'PASS','arithmetic':'exact rational SymPy',
            'input_rank':sigma.rank(),'output_rank':rho.rank(),
            'success_probability':str(p),'canonical_F3_squared':str(tau),
            'output_F3_squared':str(value),'actual_output_center':'16/25',
            'activation_success_floor_strict_upper':'97/144',
            'input_principal_minors':minors(sigma),'output_principal_minors':minors(rho),
            'kraus_contraction_minors':minors(s.eye(2)-G.conjugate().T*G)}
    assert s.trace(sigma)==s.trace(rho)==1
    Path(__file__).with_name('exact_physical_example.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if not k.endswith('minors')},indent=2))

if __name__=='__main__':main()
