#!/usr/bin/env python3
"""Exact audit in Q(k), k=1+sqrt(2), of the sharp transfer bound and tail."""

if not __debug__:
    raise RuntimeError("Certificate checks require assertions. Run Python without -O or PYTHONOPTIMIZE.")

from math import factorial
from fractions import Fraction
import json

# A pair (a,b) denotes a+b*k, with k^2=2*k+1.
def qadd(x,y):return (x[0]+y[0],x[1]+y[1])
def qneg(x):return (-x[0],-x[1])
def qmul(x,y):return (x[0]*y[0]+x[1]*y[1],x[0]*y[1]+x[1]*y[0]+2*x[1]*y[1])
def qpow(x,n):
    z=(1,0)
    for _ in range(n):z=qmul(z,x)
    return z

def padd(p,q):
    r=list(p)+[(0,0)]*max(0,len(q)-len(p))
    for i,v in enumerate(q):r[i]=qadd(r[i],v)
    return r
def pneg(p):return [qneg(v) for v in p]
def pmul(p,q):
    r=[(0,0)]*(len(p)+len(q)-1)
    for i,v in enumerate(p):
        for j,w in enumerate(q):r[i+j]=qadd(r[i+j],qmul(v,w))
    return r
def scale(p,c):return [qmul(v,c) for v in p]
def trim(p):
    p=list(p)
    while p and p[-1]==(0,0):p.pop()
    return p

k=(0,1)
D=[(2,0),(-2,0),(2,0)]
E=[(1,0),(0,0),(-1,0)]
km_u=[k,(-1,0)]
kp_u=[k,(1,0)]
k2p_u2=[qpow(k,2),(0,0),(1,0)]
P=scale(km_u,qpow(k,4))
P=padd(P,pneg(scale(pmul(pmul(D,km_u),k2p_u2),k)))
P=padd(P,pneg(scale(pmul(pmul(E,E),kp_u),qpow(k,2))))
P=padd(P,pneg(pmul([(0,0)]*4+[(1,0)],km_u)))
quotient=[(8,20),(-4,-8),(4,12)]
expected=pmul([(0,0),(1,0),(-1,0)],quotient)
assert trim(P)==trim(expected)
# Q(u)=(12k+4)+(8k+4)(1-u)+(12k+4)u^2 is positive on [0,1].
positive_decomposition=padd(padd([(4,12)],[(4,8),(-4,-8)]),[(0,0),(0,0),(4,12)])
assert trim(quotient)==trim(positive_decomposition)
kinv=(-2,1)
side=qadd(qadd(qadd((1,0),qmul((2,0),kinv)),qpow(kinv,2)),qpow(kinv,3))
assert side==qmul((5,0),kinv)

def tail_comparison(n):
    # k^n=A+B*k=(A+B)+B*sqrt(2).
    A,B=qpow(k,n)
    scale=16*factorial(n)
    rational_gap=n**n-scale*(A+B)
    radical=scale*B
    positive=rational_gap>0 and rational_gap*rational_gap>2*radical*radical
    return {'n':n,'k_power_Qk':[str(A),str(B)],
            'rational_gap':str(rational_gap),'radical_coefficient':str(radical),
            'tail_factor_below_one':positive}

at48=tail_comparison(48)
assert at48['tail_factor_below_one']
assert not tail_comparison(47)['tail_factor_below_one']
# A second threshold check uses only rational arithmetic:
# sqrt(2)<99/70, so k<169/70.
assert 99**2>2*70**2
rational_tail48=Fraction(16*factorial(48)*169**48,3360**48)
assert rational_tail48<1
# Since k<5/2 and (1+1/n)^n increases, the factor decreases after n>=6.
ratio=Fraction(5*6**6,2*7**6)
assert ratio<1
report={
    'sharp_constant':'1+sqrt(2)',
    'relation':'k^2=2*k+1',
    'central_residual_factorization_verified':True,
    'central_factor_coefficients_Qk':quotient,
    'central_positive_decomposition_verified':True,
    'side_bound':'1+2/k+1/k^2+1/k^3=5/k<k',
    'tail_at_48':at48,
    'rational_upper_bound_at_48':str(rational_tail48),
    'rational_threshold_integer_comparison':'16 * 48! * 169^48 < 3360^48',
    'tail_successive_ratio_bound_for_n_ge_6':str(ratio),
    'all_passed':True,
}
with open('sharp_bound_check.json','w') as h:json.dump(report,h,indent=2)
print(json.dumps(report,indent=2))
