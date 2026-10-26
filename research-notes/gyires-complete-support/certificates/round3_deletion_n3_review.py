#!/usr/bin/env python3
"""Independent direct-gap, exponent-tuple audit of the n=3 deletion proof.

Unlike the primary checker, this never expands in raw Birkhoff weights and
never performs a sorted-gap substitution. All matrices are built directly
in gap coordinates, and polynomial exponents are six-tuples rather than
Kronecker-encoded integers.
"""
from collections import defaultdict
from itertools import permutations
from math import factorial, prod
import json


def multiply(p,q):
    out=defaultdict(int)
    for a,x in p.items():
        for b,y in q.items():
            out[tuple(i+j for i,j in zip(a,b))]+=x*y
    return dict(out)


def add_to(dst,p,c=1):
    for a,v in p.items():dst[a]+=c*v


ps=list(permutations(range(3)))
unit=[tuple(int(i==j) for i in range(6)) for j in range(6)]
zero=(0,)*6
with open('round3_deletion_n3_birkhoff.json') as h:
    expected={tuple(r['order']):r for r in json.load(h)}
results=[]
for tail in permutations(range(1,6)):
    order=(0,)+tail
    A=[[defaultdict(int) for j in range(3)] for i in range(3)]
    for rank,vertex in enumerate(order):
        for i,j in enumerate(ps[vertex]):
            for k in range(rank+1):A[i][j][unit[k]]+=1
    p={(0,0,0):{zero:1}}
    for i in range(3):
        new={}
        for alpha,v in p.items():
            for j in range(3):
                beta=list(alpha);beta[j]+=1;beta=tuple(beta)
                if beta not in new:new[beta]=defaultdict(int)
                add_to(new[beta],multiply(v,A[i][j]))
        p=new
    b=p[(1,1,1)];G=defaultdict(int)
    add_to(G,multiply(b,b),9)
    for j in range(3):
        i,k=[v for v in range(3) if v!=j]
        a=[0]*3;a[j]=1;a[i]=2
        c=[0]*3;c[j]=1;c[k]=2
        add_to(G,multiply(p[tuple(a)],p[tuple(c)]),12)
    for alpha,v in p.items():
        add_to(G,multiply(v,v),-4*prod(factorial(x) for x in alpha))
    values=[v for v in G.values() if v]
    assert min(values)>0,(order,min(values))
    row=expected[order]
    assert len(values)==row['terms'] and min(values)==row['min']
    pure=[];zero_rays=[]
    for j in range(6):
        value=G.get(tuple(6*x for x in unit[j]),0)
        tail=[[sum(int(ps[order[k]][i]==ell) for k in range(j,6))
               for ell in range(3)] for i in range(3)]
        uniform=all(3*x==6-j for r in tail for x in r)
        assert (value==0)==uniform
        assert value>=0
        pure.append(value)
        if value==0:zero_rays.append(j)
    assert pure==row['pure_gap_sixth_coefficients']
    assert zero_rays==row['zero_pure_rays']
    results.append({'order':order,'positive_coefficients':len(values),
                    'minimum':min(values),'zero_pure_rays':zero_rays})
out={'method':'direct gap-coordinate matrices; exponent tuples; exact integers',
     'chambers':len(results),
     'positive_coefficients_checked':sum(r['positive_coefficients'] for r in results),
     'minimum_positive_coefficient':min(r['minimum'] for r in results),
     'all_primary_counts_and_minima_match':True,
     'pure_gap_coefficients_checked':6*len(results),
     'zero_pure_gap_coefficients':sum(len(r['zero_pure_rays']) for r in results),
     'zero_pure_rays_are_uniform':True,
     'all_passed':True}
with open('round3_deletion_n3_review.json','w') as h:json.dump(out,h,indent=2)
print(json.dumps(out,indent=2))
