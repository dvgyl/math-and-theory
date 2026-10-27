"""Independent direct-permanent checks of the rank-two certificate formulas.

All comparisons use Fraction. The Gyires manuscript gives the general profile reduction.
"""

if not __debug__:
    raise RuntimeError("Certificate checks require assertions. Run Python without -O or PYTHONOPTIMIZE.")

from fractions import Fraction as F
from math import factorial
from pathlib import Path
import json
import random
from rank2_bernstein import pol

def permanent(A):
    n=len(A)
    dp={0:F(1)}
    for row in A:
        nxt={}
        for mask,v in dp.items():
            for j,a in enumerate(row):
                if not(mask>>j)&1:
                    key=mask|(1<<j)
                    nxt[key]=nxt.get(key,F(0))+v*a
        dp=nxt
    return dp[(1<<n)-1]

def gram(A):
    return [[sum((a*b for a,b in zip(x,y)),F(0)) for y in A] for x in A]

def homogeneous_value(coeff,u,v):
    degree=len(coeff)-1
    return sum((F(c)*u**(degree-k)*v**k for k,c in enumerate(coeff)),F(0))

def profile(n,a,m,t):
    return [F(1)]*a+[(t-a)/m]*m+[F(0)]*(n-a-m)

def matrix(x,y,t):
    n=len(x)
    return [[r*s/t+(1-r)*(1-s)/(n-t) for s in y] for r in x]

def main():
    rng=random.Random(6620261026)
    counts={'profile_pairs':0,'direct_permanent_identity_checks':0,'singleton_interval_checks':0,'uniform_profile_checks':0}
    for n in range(2,8):
        profiles=[(a,m) for a in range(n) for m in range(1,n-a+1)]
        pairs=[(a,m,c,ell) for a,m in profiles for c,ell in profiles
               if max(a,c)<min(a+m,c+ell)]
        if n>=6:
            rng.shuffle(pairs)
            pairs=pairs[:60]
        cn=F(factorial(n),n**n)
        for a,m,c,ell in pairs:
            L=max(a,c);R=min(a+m,c+ell)
            strong,contract=pol(n,a,m,c,ell)
            counts['profile_pairs']+=1
            for u,v in [(1,1),(2,1),(1,0),(0,1)]:
                t=F(L*u+R*v,u+v)
                if not 0<t<n:
                    continue
                A=matrix(profile(n,a,m,t),profile(n,c,ell,t),t)
                assert all(sum(row)==1 for row in A)
                assert all(sum(col)==1 for col in zip(*A))
                assert all(x>=0 for row in A for x in row)
                cross=permanent(A)/cn
                noise=permanent(gram(A))/cn
                D=F((L*u+R*v)*((n-L)*u+(n-R)*v))
                den_s=factorial(n)**2*m**(2*n)*ell**(2*n)*D**(2*n)
                den_h=factorial(n)*m**(2*n)*ell**n*D**(2*n)
                assert homogeneous_value(strong,u,v)/den_s==cross**2-noise
                assert homogeneous_value(contract,u,v)/den_h==cross-noise
                counts['direct_permanent_identity_checks']+=1
                if (a,m)==(0,n) or (c,ell)==(0,n):
                    assert cross==noise==1
                    counts['uniform_profile_checks']+=1
        # Omitted single-point intervals have two identical deterministic laws.
        for h in range(1,n):
            x=[F(1)]*h+[F(0)]*(n-h)
            A=matrix(x,list(reversed(x)),F(h))
            assert permanent(A)==permanent(gram(A))
            counts['singleton_interval_checks']+=1
    result={'status':'all direct permanent identity assertions passed','counts':counts,
            'scope':'Exact checks of the homogeneous identities and boundary cases. The Gyires manuscript proves the general profile reduction.'}
    Path('rank2_identity_audit.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
