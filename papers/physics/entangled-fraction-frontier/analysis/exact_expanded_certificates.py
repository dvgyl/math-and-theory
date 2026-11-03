#!/usr/bin/env python3
"""Exact symbolic certificates for the expanded examples (SymPy rationals)."""
from pathlib import Path
import json
import sympy as s

checks=[]
def check(name,condition):
    if not bool(condition):raise AssertionError(name)
    checks.append(name)
def marginals(M,m,n):
    return (s.Matrix(m,m,lambda i,k:sum(M[i*n+j,k*n+j] for j in range(n))),
            s.Matrix(n,n,lambda j,l:sum(M[i*n+j,i*n+l] for i in range(m))))
R=s.Rational

# A whole nine-dimensional optimizer face in dimension four.
z=s.zeros(16,1)
for i,n in enumerate([4,3,2,1]):z[5*i]=R(n,6)
V=s.zeros(16,4)
for i in range(2):
    for j in range(2):V[8*i+2*j+1,2*i+j]=1
bell=s.Matrix([1,0,0,1])/s.sqrt(2)
phi=s.zeros(16,1)
for i in range(4):phi[5*i]=R(1,2)
A=s.diag(*[R(k,36) for k in [19,9,7,1]])
B=s.diag(*[R(k,36) for k in [16,12,4,4]])
for label,omega,rank in [('Bell',bell*bell.T,2),('mixed',s.eye(4)/4,5)]:
    M=z*z.T+V*omega*V.T/6
    aa,bb=marginals(M,4,4)
    check(label+' exact Alice marginal',aa==A)
    check(label+' exact Bob marginal',bb==B)
    check(label+' trace one',s.trace(M)==1)
    check(label+' exact rank',M.rank()==rank)
    check(label+' Bell overlap 25/36',(phi.T*M*phi)[0]==R(25,36))
    check(label+' local residual extraction',(V.T*M*V)*6==omega)
    check(label+' positive spectrum',all(ev>=0 for ev in M.eigenvals()))
check('not every optimizer has rank at most d',5>4)

# Exact dual multiplier certificate for this face.
ell=s.diag(R(5,8),R(5,6),R(5,4),R(5,2))
H=s.diag(0,R(5,6),0,R(5,2));K=ell-H
Z=s.kronecker_product(H,s.eye(4))+s.kronecker_product(s.eye(4),K)-phi*phi.T
check('dual objective 25/36',s.trace(H*A)+s.trace(K*B)==R(25,36))
check('dual annihilates coherent vector',Z*z==s.zeros(16,1))
check('dual annihilates residual space',Z*V==s.zeros(16,4))
check('dual kernel dimension five',16-Z.rank()==5)
xd=s.ones(4,1)/2
check('dual weighted Cauchy normalization',(xd.T*ell.inv()*xd)[0]==1)
check('dual diagonal weights positive',all(ell[i,i]>0 for i in range(4)))
check('dual off-diagonal weights nonnegative',all(H[i,i]+K[j,j]>=0 for i in range(4) for j in range(4) if i!=j))

# Boundary cross coherences: equality does not force their disappearance.
v=s.zeros(9,1);v[0]=v[5]=1/s.sqrt(2)
rho=v*v.T;aa,bb=marginals(rho,3,3)
check('singular optimizer Alice',aa==s.diag(R(1,2),R(1,2),0))
check('singular optimizer Bob',bb==s.diag(R(1,2),0,R(1,2)))
check('singular optimizer pure',rho.rank()==1)
check('singular cross nonzero',rho[0,5]==R(1,2))
x=s.zeros(9,1)
for i in range(3):x[4*i]=1/s.sqrt(3)
check('singular Bell overlap',(x.T*rho*x)[0]==R(1,6))
zz=s.zeros(9,1);zz[0]=1/s.sqrt(2)
Ha=s.Matrix(3,3,s.symbols('a0:9'));Kb=s.Matrix(3,3,s.symbols('b0:9'))
local=s.kronecker_product(Ha,s.eye(3))+s.kronecker_product(s.eye(3),Kb)
check('arbitrary local dual has zero missing diagonal coordinate',(local*zz)[4]==0)
check('target has nonzero forbidden slack coordinate',s.simplify(((local-x*x.T)*zz)[4])==-s.sqrt(2)/6)

# A positive-definite marginal pair whose unique optimum has rank d=3.
a=[R(2,3),R(1,6),R(1,6)];b=[R(1,3)]*3;m=[min(ai,bi) for ai,bi in zip(a,b)]
zc=s.zeros(9,1)
for i,mi in enumerate(m):zc[4*i]=s.sqrt(mi)
rem=s.zeros(9);rem[1,1]=rem[2,2]=R(1,6)
rank3=zc*zc.T+rem;ac,bc=marginals(rank3,3,3)
check('rank sharp example marginals',(ac==s.diag(*a)) and (bc==s.diag(*b)))
check('rank sharp example rank three',rank3.rank()==3)
check('rank sharp example both marginals positive',all(t>0 for t in a+b))

# Fixed-marginal optimization cannot be restricted to normalized pure states.
mis=s.zeros(4);mis[0,0]=mis[0,3]=mis[3,0]=mis[3,3]=R(3,10);mis[1,1]=R(2,5)
am,bm=marginals(mis,2,2)
check('misaligned pure-only counterexample marginals',am==s.diag(R(7,10),R(3,10)) and bm==s.diag(R(3,10),R(7,10)))
check('misaligned mixed optimizer overlap 3/5',(bell.T*mis*bell)[0]==R(3,5))
check('misaligned mixed optimizer positive',all(ev>=0 for ev in mis.eigenvals()))
pure_cross=s.Matrix([0,s.sqrt(R(7,10)),s.sqrt(R(3,10)),0])
check('same-marginal pure coupling overlap zero',(bell.T*pure_cross)[0]==0)

# Maximal Schmidt rank of the target is also essential for core uniqueness.
product=s.Matrix([1,0,0,0]);w0=product/s.sqrt(2);w1=bell
check('non-full-Schmidt distinct equal amplitude',(product.T*w0)[0]==(product.T*w1)[0] and w0!=w1)
aa0,bb0=marginals(w0*w0.T,2,2);aa1,bb1=marginals(w1*w1.T,2,2)
check('non-full-Schmidt both vectors feasible',all(ev>=0 for ev in (s.eye(2)/2-aa0).eigenvals()) and all(ev>=0 for ev in (s.eye(2)/2-bb0).eigenvals()) and aa1==s.eye(2)/2 and bb1==s.eye(2)/2)

# Success-frontier transition, expressed without ambiguous square-root signs.
u=s.symbols('u',nonnegative=True);c=1-u*u;L=1-c/2
transition=(1+u*u)**2/(4*L)
check('success branches meet exactly',s.simplify(transition-L)==0)
q,beta=s.symbols('q beta',positive=True)
check('success endpoint relation',s.simplify(q*(1+(1-q)/q)-1)==0)

result={'scope':'Exact symbolic certificates; no floating point arithmetic',
        'checks_passed':len(checks),'checks':checks,
        'fourdimensional_fef':'25/36','optimizer_ranks':[2,5],
        'rank_sharp_positive_marginal_example':3}
path=Path(__file__).with_name('exact_expanded_results.json')
path.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
