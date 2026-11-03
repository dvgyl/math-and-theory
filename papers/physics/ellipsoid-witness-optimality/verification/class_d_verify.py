#!/usr/bin/env python3
"""Exact independent symbolic certificates for the Class D audit.

Requires only SymPy. No floating-point computation or numerical SDP is used.
This file checks the explicit algebraic steps; it is not a substitute for the
analytic normal-form, cone-decomposition, or local-filtering arguments.
"""
import json
from pathlib import Path
import sympy as s

I2=s.eye(2)
X=s.Matrix([[0,1],[1,0]])
Y=s.Matrix([[0,-s.I],[s.I,0]])
Z=s.diag(1,-1)
pauli=[I2,X,Y,Z]
kron=s.kronecker_product
I4=s.eye(4)
XX,YY,ZZ=(kron(P,P) for P in [X,Y,Z])
checks=[]

def zero(M):
    return all(s.simplify(x)==0 for x in M)

def check(name, condition, detail=None):
    assert bool(condition), name
    entry={'check':name,'passed':True}
    if detail is not None: entry['detail']=str(detail)
    checks.append(entry)

def pt(M, side='B'):
    N=s.zeros(4)
    for a in range(2):
        for b in range(2):
            for c in range(2):
                for d in range(2):
                    if side=='B': N[2*a+b,2*c+d]=M[2*a+d,2*c+b]
                    else: N[2*a+b,2*c+d]=M[2*c+b,2*a+d]
    return N

def W(p):
    return s.Matrix([[p,0,0,0],[0,1-p,1,0],[0,1,1-p,0],[0,0,0,p]])/2

p,q=s.symbols('p q',positive=True)
e00=s.Matrix([1,0,0,0]);e01=s.Matrix([0,1,0,0]);e10=s.Matrix([0,0,1,0]);e11=s.Matrix([0,0,0,1])
phip=e00+e11;phim=e00-e11;psip=e01+e10;psim=e01-e10
Pp=psip*psip.T/2
Pm=psim*psim.T/2
check('family trace one',s.trace(W(p))==1)
check('family Pauli expansion',zero(W(p)-(I4+XX+YY+(2*p-1)*ZZ)/4))
check('family determinant',s.factor(W(p).det()+p**3*(2-p)/16)==0)
check('partial transpose determinant',s.factor(pt(W(p)).det()+(1-p)**3*(1+p)/16)==0)
for v,eig in [(e00,p/2),(e11,p/2),(psip,(2-p)/2),(psim,-p/2)]:
    check('family eigenvector '+str(list(v)),zero(W(p)*v-eig*v))
for v,eig in [(phip,(p+1)/2),(phim,(p-1)/2),(e01,(1-p)/2),(e10,(1-p)/2)]:
    check('PT eigenvector '+str(list(v)),zero(pt(W(p))*v-eig*v))
check('general refinement identity',zero(W(p)-(p/q)*W(q)-(1-p/q)*Pp))
rho=(1-(p+q)/4)*Pm+(p+q)*Pp/4
check('general strict detector lower',s.simplify(s.trace(rho*W(p))-(q-p)/4)==0)
check('general strict detector upper',s.simplify(s.trace(rho*W(q))+(q-p)/4)==0)

certificates={}
for qval in [s.Rational(3,4),s.Rational(1,3)]:
    pval=s.Rational(1,4)
    low,high=W(pval),W(qval)
    rho0=rho.subs({p:pval,q:qval})
    alpha=pval/qval
    check('rational refinement q='+str(qval),zero(low-alpha*high-(1-alpha)*Pp))
    check('detector density q='+str(qval),s.trace(rho0)==1 and all(v>=0 for v in rho0.eigenvals()))
    eval_low=s.trace(rho0*low);eval_high=s.trace(rho0*high)
    check('strict detection q='+str(qval),eval_low>0 and eval_high<0)
    check('Class D determinants q='+str(qval),all(M.det()<0 for M in [low,high,pt(low),pt(high)]))
    T=s.diag(1,1,2*qval-1)
    outer_inverse=s.diag(1,1,4)
    containment=s.diag(0,0,1-4*(2*qval-1)**2,0)
    expected=s.diag(1,1,1,0)
    expected[:3,:3]=s.eye(3)-T.T*outer_inverse*T
    check('exact containment LMI q='+str(qval),zero(containment-expected) and all(z>=0 for z in containment.diagonal()))
    certificates[str(qval)]={
      'alpha':str(alpha),'low_determinant':str(low.det()),'high_determinant':str(high.det()),
      'low_PT_determinant':str(pt(low).det()),'high_PT_determinant':str(pt(high).det()),
      'detector_expectations':[str(eval_low),str(eval_high)],
      'containment_LMI_diagonal':[str(v) for v in containment.diagonal()]
    }

# Ordinary Lorentz normal form mirror certificate.
w0,w1,w2,t=s.symbols('w0 w1 w2 t',real=True)
r=w1+w2-w0
alpha=(r-t)/(r+t)
Bminus=w0*I4+w1*ZZ+w2*XX-t*YY
Bplus=w0*I4+w1*ZZ+w2*XX+t*YY
C=w0*I4+w1*ZZ+w2*XX-r*YY
check('ordinary mirror residual identity',zero(Bminus-alpha*Bplus-(1-alpha)*C))
for label,v,eig in [('Phi+',phip,2*(w1+w2)),('Phi-',phim,2*(w0-w2)),('Psi+',psip,2*(w0-w1)),('Psi-',psim,0)]:
    check('ordinary residual eigenvalue '+label,zero(C*v-eig*v),eig)
check('ordinary chirality flip is Bob partial transpose',zero(pt(Bminus)-Bplus))

# First extraordinary Lorentz normal form mirror certificate.
k=s.symbols('k',nonnegative=True)
prod=kron(I2+Z,I2-Z)
Em=w0*(I4+ZZ)+k*prod+w2*XX-t*YY
Ep=w0*(I4+ZZ)+k*prod+w2*XX+t*YY
alpha_e=(w2-t)/(w2+t)
Ce=w0*(I4+ZZ)+w2*(XX-YY)+k*prod
check('extraordinary mirror residual identity',zero(Em-alpha_e*Ep-(1-alpha_e)*Ce))
for label,v,eig in [('Phi+',phip,2*(w0+w2)),('Phi-',phim,2*(w0-w2)),('01',e01,4*k),('10',e10,0)]:
    check('extraordinary residual eigenvalue '+label,zero(Ce*v-eig*v),eig)
check('extraordinary chirality flip is Bob partial transpose',zero(pt(Em)-Ep))

# Rank-two lifting: input Y is killed; transpose can be absorbed.
c1,c2,c3,a11,a21,a31,a13,a23,a33=s.symbols('c1 c2 c3 a11 a21 a31 a13 a23 a33',real=True)
map_pauli=[I2+c1*X+c2*Y+c3*Z,a11*X+a21*Y+a31*Z,s.zeros(2),a13*X+a23*Y+a33*Z]
def L(M):
    out=s.zeros(4)
    for i,Pi in enumerate(pauli):
        for j,Pj in enumerate(pauli):
            coeff=s.trace(kron(Pi,Pj)*M)/4
            out+=coeff*kron(map_pauli[i],Pj)
    return out
for i,Pi in enumerate(pauli):
    for j,Pj in enumerate(pauli):
        M=kron(Pi,Pj)
        check('rank2 transpose absorption basis '+str((i,j)),zero(L(M)-L(pt(M,'A'))))
G=s.Matrix(4,4,s.symbols('g0:16'))
check('full transpose then Bob PT equals Alice PT',zero(pt(G.T,'B')-pt(G,'A')))
check('rank2 map trace preservation on basis',all(s.trace(map_pauli[i])==s.trace(pauli[i]) for i in range(4)))

report={
  'arithmetic':'exact SymPy rational/symbolic arithmetic; no floats',
  'passed':len(checks),'failed':0,
  'rational_counterexamples':certificates,
  'ordinary_residual_eigenvalues':['2(w1+w2)','2(w0-w2)','2(w0-w1)','0'],
  'extraordinary_residual_eigenvalues':['2(w0+w2)','2(w0-w2)','4k','0'],
  'checks':checks,
  'scope':'Algebraic certificates only; general cone decomposition, normal-form classification, and filtering arguments are analytic inputs audited separately.'
}
output=Path(__file__).with_name('class_d_verify_output.json')
output.write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k!='checks'},indent=2))
