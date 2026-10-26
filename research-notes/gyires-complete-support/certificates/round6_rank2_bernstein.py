#!/usr/bin/env python3
"""Exact finite rank-two Gram-contraction certificate.

Every polynomial coefficient is an arbitrary-precision Python integer.
All-order reduction and coefficient identities: round6_rank2_bernstein.md.
This program is a finite certificate, not a proof for unbounded n.
"""
from math import comb,factorial
from pathlib import Path
import hashlib,json,time,random

def add(p,q):
 r=[0]*max(len(p),len(q))
 for i,v in enumerate(p):r[i]+=v
 for i,v in enumerate(q):r[i]+=v
 return r

def sc(p,c):return [c*x for x in p]
def mul(p,q):
 r=[0]*(len(p)+len(q)-1)
 for i,a in enumerate(p):
  if a:
   for j,b in enumerate(q):
    if b:r[i+j]+=a*b
 return r

def powers(p,n):
 out=[[1]]
 for _ in range(n):out.append(mul(out[-1],p))
 return out

def ep(n,a,m,L,R):
 xs=[[m*(n-L),m*(n-R)]]*a+[[n*(L-a)-m*L,n*(R-a)-m*R]]*m+[[-m*L,-m*R]]*(n-a-m)
 e=[[1]]+[[0]*(i+1) for i in range(1,n+1)]
 for used,x in enumerate(xs):
  for k in range(used+1,0,-1):e[k]=add(e[k],mul(e[k-1],x))
 return e

def pol(n,a,m,c,ell,details=False):
 L=max(a,c);R=min(a+m,c+ell)
 assert L<R
 D=[L*(n-L),L*(n-R)+R*(n-L),R*(n-R)]
 K=add(sc(D,ell),sc(mul([L-c,R-c],[ell+c-L,ell+c-R]),-n))
 ex=ep(n,a,m,L,R);ey=ep(n,c,ell,L,R)
 ds=powers(D,2*n);ks=powers(K,n)
 C=[0]*(2*n+1);G=[0]*(4*n+1)
 for k in range(n+1):
  C=add(C,sc(mul(mul(ex[k],ey[k]),ds[n-k]),(m*ell)**(n-k)*factorial(k)*factorial(n-k)))
  G=add(G,sc(mul(mul(mul(ex[k],ex[k]),ks[k]),ds[2*(n-k)]),m**(2*(n-k))*ell**(n-k)*factorial(k)*factorial(n-k)))
 strong=add(mul(C,C),sc(G,-factorial(n)*ell**n))
 contraction=add(sc(mul(C,ds[n]),m**n),sc(G,-1))
 if details:
  return {'C':C,'G':G,'D':D,'K':K,'strong':strong,'contraction':contraction,'L':L,'R':R}
 return strong,contraction

if __name__=='__main__':
 import argparse
 ap=argparse.ArgumentParser();ap.add_argument('--first',type=int,default=2);ap.add_argument('--last',type=int,default=15);ap.add_argument('--samples',type=int,default=0)
 ap.add_argument('--report',default='round6_rank2_bernstein_certificate.json')
 args=ap.parse_args()
 if args.first<2 or args.last<args.first or args.samples<0:
  raise ValueError('Require 2 <= first <= last and samples >= 0.')
 rows=[]
 rng=random.Random(620261026)
 for n in range(args.first,args.last+1):
  t0=time.time();fail=[0,0];ex=[None,None];tested=0;counts=[0,0];zero=[0,0];digest=hashlib.sha256()
  prof=[(a,m) for a in range(n) for m in range(1,n-a+1) if not(a==0 and m==n)]
  pairs=((a,m,c,l) for a,m in prof for c,l in prof) if not args.samples else ((*rng.choice(prof),*rng.choice(prof)) for _ in range(args.samples))
  for a,m,c,l in pairs:
   lo=max(a,c);hi=min(a+m,c+l)
   if lo>=hi:continue
   ps=pol(n,a,m,c,l);tested+=1
   digest.update(f'{n},{a},{m},{c},{l}:'.encode())
   for typ,p in enumerate(ps):
    counts[typ]+=len(p);zero[typ]+=sum(z==0 for z in p)
    digest.update((','.join(map(str,p))+';').encode())
    if min(p)<0:
     fail[typ]+=1
     if ex[typ] is None:ex[typ]={'profile':[a,m,c,l],'min':str(min(p)),'index':p.index(min(p))}
  record={'n':n,'tested':tested,'fail_strong_contraction':fail,'coefficient_counts_strong_contraction':counts,'zero_coefficient_counts_strong_contraction':zero,'coefficient_sha256':digest.hexdigest(),'examples':ex,'seconds':time.time()-t0}
  rows.append(record)
  print(json.dumps(record),flush=True)
  report={'status':'passed' if all(not any(row['fail_strong_contraction']) for row in rows) else 'failed',
          'arithmetic':'exact Python integers','exhaustive_profile_pairs':args.samples==0,
          'first_order':args.first,'last_completed_order':n,'requested_last_order':args.last,
          'scope':'Whole-interval finite coefficient certificate; no assertion for unbounded order.',
          'records':rows}
  Path(args.report).write_text(json.dumps(report,indent=2)+'\n')
  if any(fail):
   raise RuntimeError('A negative exact coefficient was found; this certificate failed.')
