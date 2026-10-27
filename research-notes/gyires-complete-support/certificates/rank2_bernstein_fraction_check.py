#!/usr/bin/env python3
"""Independent rational power-basis construction and exact coefficient comparison.

This implementation starts from polynomials in the mean t, independently of
the homogeneous integer construction, then converts to the Bernstein basis.
"""
from fractions import Fraction as F
from math import comb,factorial
from pathlib import Path
import argparse,json,time

def add(p,q):
 r=[F(0)]*max(len(p),len(q))
 for i,v in enumerate(p):r[i]+=v
 for i,v in enumerate(q):r[i]+=v
 while len(r)>1 and r[-1]==0:r.pop()
 return r

def sc(p,c):return [c*x for x in p]
def mul(p,q):
 r=[F(0)]*(len(p)+len(q)-1)
 for i,a in enumerate(p):
  if a:
   for j,b in enumerate(q):
    if b:r[i+j]+=a*b
 return r

def pw(p,n):
 r=[F(1)]
 for _ in range(n):r=mul(r,p)
 return r

def ep(n,a,m):
 xs=[[F(1),F(-1,n)]]*a+[[F(-a,m),F(1,m)-F(1,n)]]*m+[[F(0),F(-1,n)]]*(n-a-m)
 e=[[F(1)]]+[[F(0)] for _ in range(n)]
 for used,x in enumerate(xs):
  for k in range(used+1,0,-1):e[k]=add(e[k],mul(e[k-1],x))
 return e

def bern(p,lo,hi,N):
 out=[F(0)]*(N+1)
 for k,co in enumerate(p):
  for j in range(k+1):out[j]+=co*comb(k,j)*lo**(k-j)*(hi-lo)**j
 return [sum(out[j]*F(comb(i,j),comb(N,j)) for j in range(i+1)) for i in range(N+1)]

def pol(n,a,m,c,ell):
 D=[F(0),F(n),F(-1)];u=ep(n,a,m);v=ep(n,c,ell)
 K=add(D,sc(mul([F(-c),F(1)],[F(ell+c),F(-1)]),F(-n,ell)))
 ds=[pw(D,k) for k in range(2*n+1)];ks=[pw(K,k) for k in range(n+1)]
 C=[F(0)];G=[F(0)]
 for k in range(n+1):
  fact=F(n**(2*k),comb(n,k))
  C=add(C,sc(mul(mul(u[k],v[k]),ds[n-k]),fact))
  G=add(G,sc(mul(mul(mul(u[k],u[k]),ks[k]),ds[2*(n-k)]),fact))
 return add(mul(C,C),sc(G,-1)),add(mul(C,ds[n]),sc(G,-1))

if __name__=='__main__':
 from rank2_bernstein import pol as integer_pol
 ap=argparse.ArgumentParser();ap.add_argument('--first',type=int,default=2);ap.add_argument('--last',type=int,default=6)
 ap.add_argument('--report',default='rank2_fraction_comparison.json');args=ap.parse_args()
 if args.first<2 or args.last<args.first:
  raise ValueError('Require 2 <= first <= last.')
 records=[]
 Path(args.report).write_text(json.dumps({'status':'running','first_order':args.first,'requested_last_order':args.last,'records':[]},indent=2)+'\n')
 for n in range(args.first,args.last+1):
  t0=time.time();fail=[0,0];ex=[None,None];tested=0;compared=0
  prof=[(a,m) for a in range(n) for m in range(1,n-a+1) if not(a==0 and m==n)]
  expected={(a,m,c,l) for a,m in prof for c,l in prof if max(a,c)<min(a+m,c+l)}
  # There are 2*binom(n+2,4) ordered pairs with disjoint interval interiors.
  if len(expected) != (n*(n+1)//2-1)**2-2*comb(n+2,4):
   raise ArithmeticError('Incomplete expected profile set.')
  checked=set()
  for a,m in prof:
   for c,l in prof:
    lo=max(a,c);hi=min(a+m,c+l)
    if lo>=hi:continue
    key=(a,m,c,l)
    if key in checked:
     raise ArithmeticError('Duplicate profile interval.')
    checked.add(key)
    ps=pol(n,a,m,c,l);ip=integer_pol(n,a,m,c,l);tested+=1
    if len(ps)!=2 or len(ip)!=2 or any(len(p)!=4*n+1 for p in ip):
     raise ArithmeticError('Incomplete coefficient vectors.')
    scales=[(factorial(n)*m**n*l**n)**2,factorial(n)*m**(2*n)*l**n]
    for typ,p in enumerate(ps):
     bb=bern(p,lo,hi,4*n)
     for i,value in enumerate(bb):
      if value*comb(4*n,i)*scales[typ] != ip[typ][i]:
       raise ArithmeticError(f'Coefficient mismatch: {(n,a,m,c,l,typ,i)}')
      compared+=1
     if min(bb)<0:
      fail[typ]+=1
      if ex[typ] is None:ex[typ]={'profile':[a,m,c,l],'min':str(min(bb)),'index':bb.index(min(bb))}
  if not tested or checked != expected or compared != 2*tested*(4*n+1):
   raise ArithmeticError('Incomplete rational coefficient coverage.')
  record={'n':n,'tested':tested,'coefficients_compared_exactly':compared,'fail_strong_contraction':fail,'examples':ex,'seconds':time.time()-t0}
  records.append(record);print(json.dumps(record),flush=True)
  report={'status':'failed' if any(fail) else 'running',
       'arithmetic':'exact fractions and integers','exhaustive_profile_pairs':True,
       'first_order':args.first,'requested_last_order':args.last,'last_completed_order':n,'records':records}
  Path(args.report).write_text(json.dumps(report,indent=2)+'\n')
  if any(fail):raise ArithmeticError('Negative Bernstein coefficient found.')

 if [row['n'] for row in records] != list(range(args.first,args.last+1)):
  raise ArithmeticError('Incomplete requested order range.')
 report['status']='passed'
 Path(args.report).write_text(json.dumps(report,indent=2)+'\n')
