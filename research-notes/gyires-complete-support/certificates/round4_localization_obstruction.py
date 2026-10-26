#!/usr/bin/env python3
"""Exact arithmetic checks for the multivariate localization obstruction."""
from fractions import Fraction as F
from itertools import permutations,combinations
from math import factorial
import json


def add(p,q):
    r=[F(0)]*max(len(p),len(q))
    for i,v in enumerate(p):r[i]+=v
    for i,v in enumerate(q):r[i]+=v
    while len(r)>1 and r[-1]==0:r.pop()
    return r

def mul(p,q):
    r=[F(0)]*(len(p)+len(q)-1)
    for i,a in enumerate(p):
        for j,b in enumerate(q):r[i+j]+=a*b
    while len(r)>1 and r[-1]==0:r.pop()
    return r

def scale(p,c):return [c*v for v in p]

def ev(p,t):return sum(v*t**i for i,v in enumerate(p))

def det(H):
    out=[F(0)];n=len(H)
    for s in permutations(range(n)):
        inversions=sum(s[i]>s[j] for i in range(n) for j in range(i+1,n))
        v=[F((-1)**inversions)]
        for i,j in enumerate(s):v=mul(v,H[i][j])
        out=add(out,v)
    return out


def main():
    # p_t=p_0+t*(x-y)*(x-z)*(y-z).
    coeff={(2,1,0):[F(1),F(1)],(2,0,1):[F(1),F(-1)],
           (1,2,0):[F(1),F(-1)],(1,0,2):[F(1),F(1)],
           (0,2,1):[F(1),F(1)],(0,1,2):[F(1),F(-1)],
           (1,1,1):[F(2)]}
    mass=[F(0)]
    for p in coeff.values():mass=add(mass,p)
    assert mass==[8]
    balance=[];marginals=[];hessians=[];minors=[]
    for j in range(3):
        mean=[F(0)];marg=[[F(0)] for _ in range(4)]
        for a,p in coeff.items():
            mean=add(mean,scale(p,a[j]));marg[a[j]]=add(marg[a[j]],p)
        assert mean==[8];assert marg==[[2],[4],[2],[0]]
        balance.append(mean);marginals.append(marg)
        H=[[[F(0)] for _ in range(3)] for _ in range(3)]
        beta=[0,0,0];beta[j]=1
        for i in range(3):
            for k in range(3):
                a=beta.copy();a[i]+=1;a[k]+=1;a=tuple(a)
                H[i][k]=scale(coeff.get(a,[F(0)]),factorial(a[0])*factorial(a[1])*factorial(a[2]))
        assert det(H)==[0,0,-64]
        ms=[]
        for i,k in combinations(range(3),2):
            minor=add(mul(H[i][i],H[k][k]),scale(mul(H[i][k],H[k][i]),-1))
            # These are -4(1+t)^2, -4(1-t)^2, or -4t^2.
            assert minor in [[-4,-8,-4],[-4,8,-4],[0,0,-4]]
            ms.append(minor)
        hessians.append(H);minors.append(ms)
    N=[F(0)]
    for a,p in coeff.items():N=add(N,scale(mul(p,p),factorial(a[0])*factorial(a[1])*factorial(a[2])))
    assert N==[16,0,12]
    t=F(1,2);normalized_N=ev(N,t)/64;center_square=F(1,16)
    failure=F(2,9)*normalized_N-center_square
    assert normalized_N==F(19,64) and failure==F(1,288)
    # First-order kernel compression and balance reduce any supported
    # center-preserving direction to coefficients(a,-a,-a,a,a,-a).
    V={(2,1,0):1,(2,0,1):-1,(1,2,0):-1,(1,0,2):1,(0,2,1):1,(0,1,2):-1}
    for j in range(3):assert sum((a[j]-1)*v for a,v in V.items())==0
    out={'status':'exact symbolic rational verification',
         'coefficient_polynomials':[[list(a),[str(v) for v in p]] for a,p in coeff.items()],
         'derivative_hessian_determinant_polynomial':[0,0,-64],
         'all_two_by_two_principal_minors':[[[str(v) for v in p] for p in ms] for ms in minors],
         'norm_polynomial':[16,0,12],
         'coordinate_marginal_polynomial':[2,4,2,0],
         't_half_normalized_norm':str(normalized_N),'t_half_center_square':str(center_square),
         't_half_strong_gap_wrong_direction':str(failure),
         'supported_tangent_direction_coefficients':[[list(a),v] for a,v in V.items()]}
    with open('round4_localization_obstruction.json','w') as f:json.dump(out,f,indent=2)
    print(json.dumps({'all_derivative_determinants':'-64 t^2','norm':'16+12t^2',
                      'normalized_strong_failure_at_t_half':str(failure)},indent=2))

if __name__=='__main__':main()
