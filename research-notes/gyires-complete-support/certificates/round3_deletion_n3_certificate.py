#!/usr/bin/env python3
"""Exact all-DS3 certificate for average capacity-balanced deletion.

The 120 sorted Birkhoff chambers cover all 720 by row-permutation invariance.
This proves the n=3 product-input lemma, not its unrestricted stable extension.
"""
from itertools import permutations,product
from collections import defaultdict
from math import factorial
from math import comb

def polyaddprod(dst,p,q,scale=1):
 for a,x in p.items():
  for b,y in q.items():dst[a+b]+=scale*x*y

def gap_transform(d,u,base,order):
 rank={v:i for i,v in enumerate(order)}
 d={sum((k//u[j]%base)*u[rank[j]] for j in range(len(u))):v for k,v in d.items()}
 for j in range(len(u)-1,0,-1):
  out=defaultdict(int)
  for k,v in d.items():
   e=k//u[j]%base
   for h in range(e+1):out[k-h*u[j]+h*u[j-1]]+=v*comb(e,h)
  d={k:v for k,v in out.items()if v}
 return d
import time,json
ps=list(permutations(range(3)));base=7;u=[base**i for i in range(6)]
A=[[{} for _ in range(3)]for _ in range(3)]
for k,p in enumerate(ps):
 for i,j in enumerate(p):A[i][j][u[k]]=1
poly={}
for js in product(range(3),repeat=3):
 al=tuple(js.count(j)for j in range(3));v={0:1}
 for i,j in enumerate(js):
  q=defaultdict(int);polyaddprod(q,v,A[i][j]);v=q
 q=poly.setdefault(al,defaultdict(int))
 for k,c in v.items():q[k]+=c
b=poly[(1,1,1)];gap=defaultdict(int);polyaddprod(gap,b,b,9)
for j in range(3):
 other=[i for i in range(3)if i!=j];a=[0]*3;a[j]=1;a[other[0]]=2;c=[0]*3;c[j]=1;c[other[1]]=2
 polyaddprod(gap,poly[tuple(a)],poly[tuple(c)],12)
for al,p in poly.items():polyaddprod(gap,p,p,-4*__import__('math').prod(factorial(x)for x in al))
gap={k:v for k,v in gap.items() if v}
print('rawterms',len(gap),flush=True)
t=time.time();reports=[]
for tail in permutations(range(1,6)):
 order=(0,)+tail;g=gap_transform(gap,u,base,order);neg=[(k,v)for k,v in g.items()if v<0]
 pure=[];zero_rays=[]
 for j in range(6):
  value=g.get(6*u[j],0)
  tail=[[sum(int(ps[order[k]][i]==ell)for k in range(j,6))for ell in range(3)]for i in range(3)]
  uniform=all(3*x==6-j for row in tail for x in row)
  assert (value==0)==uniform,(order,j,value,tail)
  assert value>=0
  pure.append(value)
  if value==0:zero_rays.append(j)
 reports.append({'order':order,'terms':len(g),'negative':len(neg),'min':min(g.values()),'pure_gap_sixth_coefficients':pure,'zero_pure_rays':zero_rays,'zero_pure_rays_are_uniform':True})
 if neg:
  print('NEGATIVE',reports[-1],[(tuple(k//v%base for v in u),c)for k,c in neg[:10]],flush=True);break
else:print('ALLPASS',len(reports),'minimum',min(r['min']for r in reports),flush=True)
print('seconds',time.time()-t,flush=True)
with open('round3_deletion_n3_birkhoff.json','w')as h:json.dump(reports,h,indent=2)
