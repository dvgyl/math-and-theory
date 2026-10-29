#!/usr/bin/env python3
"""Exact arithmetic certificates accompanying the written Motzkin proof.

Python standard library only. This is NOT a Lean verification or a proof assistant.
It checks polynomial identities, positive-coefficient certificates, and all finite
base cases used in the accompanying universal mathematical argument.
"""
from __future__ import annotations
from fractions import Fraction as Q
from math import gcd
import json

# Integer polynomials in n, coefficients in increasing degree order.
def trim(p):
    p=list(p)
    while len(p)>1 and p[-1]==0: p.pop()
    return tuple(p)
def add(a,b):
    return trim([(a[i] if i<len(a) else 0)+(b[i] if i<len(b) else 0)
                 for i in range(max(len(a),len(b)))])
def neg(a): return tuple(-x for x in a)
def sub(a,b): return add(a,neg(b))
def mul(a,b):
    out=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b): out[i+j]+=x*y
    return trim(out)
def scale(c,a): return trim([c*x for x in a])
def power(a,k):
    out=(1,)
    while k:
        if k&1: out=mul(out,a)
        a=mul(a,a);k//=2
    return out
def shift(a,k):
    out=(0,)
    for c in reversed(a): out=add(mul(out,(k,1)),(c,))
    return out
def value(a,k):
    out=0
    for c in reversed(a): out=out*k+c
    return out

def check(condition,message):
    if not condition: raise ArithmeticError(message)

class RF:
    """Rational functions over integer polynomials, equality by cross products."""
    def __init__(self,num=(0,),den=(1,)):
        if isinstance(num,int): num=(num,)
        if isinstance(den,int): den=(den,)
        self.num=trim(num);self.den=trim(den)
        check(self.den!=(0,), 'zero polynomial denominator')
    @staticmethod
    def cast(x): return x if isinstance(x,RF) else RF(x)
    def __add__(self,o):
        o=RF.cast(o);return RF(add(mul(self.num,o.den),mul(o.num,self.den)),mul(self.den,o.den))
    __radd__=__add__
    def __neg__(self): return RF(neg(self.num),self.den)
    def __sub__(self,o):return self+-RF.cast(o)
    def __rsub__(self,o):return RF.cast(o)+-self
    def __mul__(self,o):
        o=RF.cast(o);return RF(mul(self.num,o.num),mul(self.den,o.den))
    __rmul__=__mul__
    def __truediv__(self,o):
        o=RF.cast(o);return RF(mul(self.num,o.den),mul(self.den,o.num))
    def __rtruediv__(self,o):return RF.cast(o)/self
    def __pow__(self,k):return RF(power(self.num,k),power(self.den,k))
    def __eq__(self,o):
        o=RF.cast(o);return mul(self.num,o.den)==mul(o.num,self.den)

N=(0,1);m=(3,1)
p_lower=(-1790,1599,1687,304)
p_upper=(-1331,-509,112)
d_lower=scale(16,mul(power(m,3),(146,297,216,48)))
d_upper=scale(16,mul(power(m,3),(19,40,16)))
P=(4660409556032,24132003073520,56628081108524,
   79753800966621,75163688028504,49975719381810,
   24049942325892,8443039471929,2146478817312,
   385445807712,46409331456,3364180992,111034368)

x=RF(N)
def L(x):return 3-9/(2*(x+3))+9/(16*(x+3)**2)
def U(x):return L(x)+2/(x+3)**3
def err(x):return 1/(8*(x+3)**2)
def f(x,r,e):return (x+1)/(x+3)*(2+3/r)+2*e/(x+3)
# Coarse envelope and growth identities used before the sharper induction.
check(f(x,RF(3),-1/x)-(3-6/x)==16/(x*(x+3)), 'coarse lower identity')
check(3-f(x,3-6/(x-1),1/x)==(4*x*x-22*x+6)/(x*(x+3)*(x-3)), 'coarse upper identity')
check(all(c>0 for c in shift((6,-22,4),9)), 'coarse upper positivity')
check(2*(x+3)**2-(x+4)**2==x*x+4*x+2, 'growth induction identity')
check(f(x,U(x-1),-err(x))-L(x)==RF(p_lower,d_lower),'lower induction identity')
check(U(x)-f(x,L(x-1),err(x))==RF(p_upper,d_upper),'upper induction identity')
# Both numerators and denominators are strictly positive at n >= 13.
for name,p in [('lower numerator',p_lower),('upper numerator',p_upper),
               ('lower denominator',d_lower),('upper denominator',d_upper)]:
    q=shift(p,13)
    check(all(c>=0 for c in q) and q[0]>0, name+' shifted positivity')

# Algebraic identity for F_n(U(n),-err(n)).
D=scale(16,power(m,3))
V=add(add(sub(scale(48,power(m,3)),scale(72,power(m,2))),scale(9,m)),(32,))
Y=sub(mul((2,1),add(scale(2,V),scale(3,D))),scale(4,m))
Z=add(mul(m,add(scale(2,Y),scale(3,mul(V,(4,1))))),scale(4,mul(m,(4,1))))
identity_left=sub(mul(mul((5,1),D),power(Y,3)),mul(mul(power((4,1),2),power(V,3)),Z))
check(identity_left==mul(m,P),'degree-12 polynomial certificate')
check(all(c>0 for c in P),'all coefficients of P must be positive')
# Independent rational-function expression of the same identity.
r=U(x);e=-err(x)
y=((x+2)*(2*r+3)+2*e)/(x+4)
z=((x+3)*(2*y+3*r)-2*e)/(x+5)
check(y**3-r**3*z==RF(P,scale(65536,mul(mul(power(m,11),power((4,1),3)),(5,1)))),'F rational identity')

# Range and derivative bounds for n >= 12 used in the written proof.
check(L(x)-RF(8,3)==RF((-477,-120,16),scale(48,power(m,2))),'L >= 8/3 identity')
check(3-U(x)==RF((589,423,72),scale(16,power(m,3))),'U < 3 identity')
check(all(c>0 for c in shift((-477,-120,16),12)), 'L >= 8/3 positivity')
check(Q(486)-3*Q(8,3)**2*19-Q(8,3)**3*5==-Q(382,27),'negative x derivative bound')
# Coefficient of d/d epsilon is 6(n+5)y^2 - 2(n+2)x^3.
check(sub(scale(6*49,(5,1)),scale(2*27,(2,1)))==(1362,240),'positive epsilon derivative bound')
# Exact polynomial positivity for the elementary monotonicity estimates.
check(all(c>0 for c in shift((-1703,200),12)), 'lower y bound including epsilon')
check(all(c>0 for c in shift((-1451,150),12)), 'lower z bound including epsilon')
check(all(c>0 for c in shift((-40,-4,2),12)), 'z_x >= 5')
check((x+3)*(7*x+20)/((x+4)*(x+5))-5==(2*x*x-4*x-40)/((x+4)*(x+5)), 'z_x bound identity')
# Coefficients of b_(n-1), b_n, b_(n+1), b_(n+2) in D_(n+1)-D_n.
check(x*(x+1)==x*(x+1), 'log transfer first coefficient')
check(-(x+1)*(x+2)-2*(x*x-1)==-3*x*(x+1), 'log transfer second coefficient')
check(2*((x+1)**2-1)+x*(x-1)==3*x*(x+1), 'log transfer third coefficient')
check(-(x+1)*x==-x*(x+1), 'log transfer last coefficient')

# Generate all finite values independently from the Motzkin recurrence.
M=[1,1]
for n in range(1,35):
    numerator=(2*n+3)*M[n]+3*n*M[n-1]
    check(numerator%(n+3)==0, 'nonintegral Motzkin value')
    M.append(numerator//(n+3))
T=[1]
for n in range(1,len(M)):T.append(M[n]-T[-1])
for n in range(2,len(T)):
    check((n+2)*T[n]==n*(2*T[n-1]+3*T[n-2])+2*(-1)**n,'finite recurrence cross-check')
check(T[8]>=8 and Q(3)-Q(6,8)<Q(T[9],T[8])<3,'coarse-ratio induction base')
check(T[10]>=8*13**2,'growth-bound induction base')
check(L(Q(12))<Q(T[13],T[12])<U(Q(12)),'refined-ratio induction base')
q_checks={}
for n in [10,11]:
    gap=T[n]*T[n+2]**3-T[n+1]**3*T[n+3]
    check(gap>0,'finite ratio log-concavity')
    q_checks[str(n)]=str(gap)
root_checks={}
for n in range(6,12):
    exponents=(2*(n*n-1),n*(n+1),n*(n-1))
    g=gcd(gcd(exponents[0],exponents[1]),exponents[2])
    a,b,c=(j//g for j in exponents)
    left=T[n]**a;right=T[n-1]**b*T[n+1]**c
    check(left>right,'finite root log-concavity')
    root_checks[str(n)]={'exponents':[a,b,c],'left_digits':len(str(left)),
                         'right_digits':len(str(right)),'strictly_positive_gap':True}
check(T[5]**24<T[4]**15*T[6]**10,'sharp failure at center n=5')
check(T[9]*T[11]**3<T[10]**3*T[12],'sharp ratio failure at n=9')

# Test sensitivity of polynomial and finite-case checks.
corrupt=list(P);corrupt[0]+=1
check(identity_left!=mul(m,corrupt),'corruption must be rejected')
check(not(T[5]**24>=T[4]**15*T[6]**10),'reversed false base must be rejected')
report={'status':'all_exact_checks_passed','proof_assistant':'none',
        'lean_verified':False,'floating_point_used':False,
        'polynomial_certificate_degree':12,
        'refined_ratio_base_n':12,
        'refined_ratio_base_values':{'T12':T[12],'T13':T[13],
          'lower':str(L(Q(12))),'ratio':str(Q(T[13],T[12])), 'upper':str(U(Q(12)))},
        'finite_ratio_gaps':q_checks,'finite_root_checks':root_checks,
        'negative_controls_passed':2,
        'scope':'Exact certificates supporting the accompanying written universal proof; not a Lean formalization.'}
print(json.dumps(report,indent=2))
