from itertools import permutations
from math import comb, prod
from fractions import Fraction as F
from collections import defaultdict
import json, sys
import sympy as S
import mpmath as mp

mp.mp.dps=100
A=S.Matrix([[5,0,0,4,1],[0,5,0,-1,4],[0,0,1,0,0],[4,-1,0,5,0],[1,4,0,0,5]])
coeff=defaultdict(int)
terms=[]
for p in permutations(range(5)):
    value=prod(A[i,p[i]] for i in range(5))
    if value:
        inversions=sum(p[i]>p[j] for i in range(5) for j in range(i+1,5))
        coeff[inversions]+=int(value)
        terms.append([p,inversions,int(value)])
expected={0:625,3:25,5:800,7:25,8:256,9:-32,10:1}
assert dict(coeff)==expected
p14=sum(c*14**k for k,c in coeff.items())
p15=sum(c*15**k for k,c in coeff.items())
d15=sum(k*c*15**(k-1) for k,c in coeff.items() if k)
assert (p14,p15,d15)==(8968822249,7441960000,-1563030000)
L,D=A.LDLdecomposition(hermitian=False)
assert L*D*L.T==A and all(D[i,i]>0 for i in range(5))
family=[]
q=S.symbols('q')
for m in range(5):
    n=m+4
    T=S.eye(n)
    active=[0,1,m+2,m+3]
    core=S.Matrix([[4,0,2,1],[0,4,-1,2],[2,-1,4,0],[1,2,0,4]])
    for i in range(4):
        for j in range(4):T[active[i],active[j]]=core[i,j]
    cs=defaultdict(int)
    for p in permutations(range(n)):
        value=prod(T[i,p[i]] for i in range(n))
        if value:
            inv=sum(p[i]>p[j] for i in range(n) for j in range(i+1,n))
            cs[inv]+=int(value)
    predicted=4**4+4**2*q**(2*m+1)*(1+8*q**2+q**4)+q**(4*m+4)*(4-q)**2
    assert S.expand(predicted-sum(c*q**k for k,c in cs.items()))==0
    family.append({'m':m,'n':n,'polynomial':str(S.expand(predicted))})
growth=[]
for r in [F(101,100),F(11,10),F(3,2),F(2),F(15)]:
    m=1
    while r**(2*m+5) <= (4*m+4)*(2*m+5)*(5*r/4+2)*(1+F(5,2)*r**3+r**4):m+=1
    K=4*m+4
    H=2*m+1
    t=r*(1+F(1,K))
    derivative=(t+2)*r**(H-1)*(H+2*t*(H+2)*r*r+(H+4)*r**4)-r**(K+1)/K
    assert derivative<0
    growth.append({'r':str(r),'m':m,'dimension':m+4,'derivative_negative':True})

print(json.dumps({"python":sys.version,"sympy":S.__version__,"nonzero_terms":terms,"coefficient_map":expected,"p14":p14,"p15":p15,"derivative_at_15":d15,"ldl_diagonal":[str(D[i,i]) for i in range(5)],"family_cases":family,"growth_cases":growth,"status":"PASS"},indent=2))
