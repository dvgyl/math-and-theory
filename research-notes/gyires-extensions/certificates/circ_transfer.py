#!/usr/bin/env python3
"""Exact sparse-band all-order search using a finite transfer matrix.

For C=a P^-1+b I+c P, compute per(C) and per(CC^T)
in all degrees up to N; inspect every sorting chamber of a,b,c.
All other circulant weights are zero. This does not enumerate full chambers.
"""

if not __debug__:
    raise RuntimeError("Certificate checks require assertions. Run Python without -O or PYTHONOPTIMIZE.")

from collections import defaultdict
from itertools import permutations
from math import factorial
from circ_gap_test import polyaddprod,gap_transform,permanent_poly
import json,sys,time

def add(dst,p,scale=1):
    for k,v in p.items():dst[k]+=scale*v

def transfer(weights):
    r=(len(weights)-1)//2;count=1<<(2*r)
    edges=[[] for _ in range(count)]
    for mask in range(count):
        for j,p in enumerate(weights):
            if mask>>j&1:continue
            q=mask|(1<<j)
            if not(q&1):continue
            if p:edges[mask].append((q>>1,p))
    return edges

def advance(power,edges):
    count=len(edges)
    out=[[None]*count for _ in range(count)]
    for i in range(count):
        for j,p in enumerate(power[i]):
            if not p:continue
            for k,q in edges[j]:
                if out[i][k] is None:out[i][k]=defaultdict(int)
                polyaddprod(out[i][k],p,q)
    return out

def trace(power):
    out=defaultdict(int)
    for i,row in enumerate(power):
        if row[i]:add(out,row[i])
    return out

def identity(count):
    return [[{0:1} if i==j else None for j in range(count)] for i in range(count)]

if __name__=='__main__':
    if len(sys.argv)>2:
        raise ValueError('Usage: circ_transfer.py [MAX_ORDER]')
    N=int(sys.argv[1]) if len(sys.argv)>1 else 40
    if N < 5:
        raise ValueError('Maximum order must be at least five.')
    b=2*N+1;u=[b**i for i in range(3)]
    a,bb,c=[{x:1} for x in u]
    d={2*x:1 for x in u};e={u[0]+u[1]:1,u[1]+u[2]:1};f={u[0]+u[2]:1}
    Cedges=transfer([a,bb,c]);Gedges=transfer([f,e,d,e,f])
    CP=identity(4);GP=identity(16);t=time.time()
    reports=[]
    for n in range(1,N+1):
        CP=advance(CP,Cedges);GP=advance(GP,Gedges)
        if n<5:continue
        p=trace(CP);q=trace(GP)
        if n in (5,6):
            ws=[{} for _ in range(n)];ws[0]=bb;ws[1]=c;ws[-1]=a
            pd=permanent_poly([[ws[(j-i)%n] for j in range(n)] for i in range(n)])
            assert dict(pd)==dict(p),('C mismatch',n)
            gs=[]
            for s in range(n):
                gg=defaultdict(int)
                for i in range(n):polyaddprod(gg,ws[i],ws[(i+s)%n])
                gs.append(gg)
            qd=permanent_poly([[gs[(j-i)%n] for j in range(n)] for i in range(n)])
            assert dict(qd)==dict(q),('Gram mismatch',n)
        defect=defaultdict(int);polyaddprod(defect,p,p,n**n)
        for k,v in q.items():defect[k]-=factorial(n)*v
        defect={k:v for k,v in defect.items() if v}
        mins=[];checked=set()
        for perm in permutations(range(3)):
            if perm in checked:
                raise ArithmeticError('Duplicate sorting chamber.')
            checked.add(perm)
            gap=gap_transform(defect,u,b,perm)
            if not gap:
                raise ArithmeticError('Empty transformed polynomial.')
            neg=[(k,v) for k,v in gap.items() if v<0]
            mins.append(min(gap.values()))
            if neg:
                report={'n':n,'order':perm,'negative_count':len(neg),'examples':[{'exponents':[k//x%b for x in u],'coefficient':v} for k,v in neg[:8]]}
                print(json.dumps(report),flush=True)
                with open('circ_transfer_negative.json','w') as h:json.dump(report,h,indent=2)
                raise ArithmeticError('A negative exact coefficient was found.')
        if checked != {(0,1,2),(0,2,1),(1,0,2),(1,2,0),(2,0,1),(2,1,0)}:
            raise ArithmeticError('Incomplete sorting chamber coverage.')
        reports.append({'n':n,'chambers':6,'min_coefficient':min(mins),'original_terms':len(defect)})
        print(json.dumps({'n':n,'all_six_pass':True,'min_coefficient':min(mins),'seconds':time.time()-t}),flush=True)
    if [r['n'] for r in reports] != list(range(5,N+1)):
        raise ArithmeticError('Incomplete order coverage.')
    with open('circ_transfer_results.json','w') as h:json.dump(reports,h,indent=2)
