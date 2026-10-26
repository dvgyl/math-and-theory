#!/usr/bin/env python3
"""Independent direct-permanent checks of the homogeneous certificate identities.

This finite identity check is not the complete profile certificate.
"""
from fractions import Fraction as F
from math import factorial
from collections import defaultdict
from pathlib import Path
import random,json
from round6_rank2_bernstein import pol

def permanent(A):
    values={0:F(1)}
    for row in A:
        nxt=defaultdict(F)
        for mask,value in values.items():
            for j,a in enumerate(row):
                if not mask>>j&1:nxt[mask|1<<j]+=value*a
        values=nxt
    return values[(1<<len(A))-1]

def gram(A):return [[sum((a*b for a,b in zip(row,col)),F()) for col in A] for row in A]
def stochastic(A):return all(x>=0 for row in A for x in row) and all(sum(row)==1 for row in A) and all(sum(col)==1 for col in zip(*A))
def evalh(coeff,U,V):
    degree=len(coeff)-1
    return sum(c*U**(degree-i)*V**i for i,c in enumerate(coeff))

def main():
    rng=random.Random(6261028);counts={}
    for n in range(2,8):
        count=0
        profiles=[(a,m) for a in range(n) for m in range(1,n-a+1)]
        pairs=[(a,m,c,l) for a,m in profiles for c,l in profiles if max(a,c)<min(a+m,c+l)]
        for a,m,c,l in rng.sample(pairs,min(15,len(pairs))):
            L=max(a,c);R=min(a+m,c+l)
            S,H=pol(n,a,m,c,l)
            for U,V in [(1,2),(0,1),(1,0)]:
                t=F(L*U+R*V,U+V)
                if t in [0,n]:continue
                x=[F(1)]*a+[F(t-a,m)]*m+[F(0)]*(n-a-m)
                y=[F(1)]*c+[F(t-c,l)]*l+[F(0)]*(n-c-l)
                A=[[xi*yj/t+(1-xi)*(1-yj)/(n-t) for yj in y] for xi in x]
                assert stochastic(A)
                P=permanent(A);G=permanent(gram(A));cn=F(factorial(n),n**n)
                D=(L*U+R*V)*((n-L)*U+(n-R)*V)
                denH=factorial(n)*m**(2*n)*l**n*D**(2*n)
                denS=factorial(n)**2*m**(2*n)*l**(2*n)*D**(2*n)
                assert evalh(H,U,V)*cn==denH*(P-G)
                assert evalh(S,U,V)*cn**2==denS*(P**2-cn*G)
                count+=1
        counts[n]=count
    report={'status':'all exact rational identities passed','total':sum(counts.values()),'counts_by_order':counts,'scope':'independent finite checks of certificate identities against direct permanents; not full profile enumeration or proof-assistant verification'}
    Path('round6_rank2_boundary_audit.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))
if __name__=='__main__':main()
