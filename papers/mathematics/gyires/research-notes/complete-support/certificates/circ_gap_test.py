#!/usr/bin/env python3
"""Exact circulant Gyires strong-defect coefficient investigations."""
from collections import defaultdict
from itertools import permutations
from math import comb, factorial, gcd
import json, sys, time

def polyaddprod(dst, p, q, scale=1):
    for a, x in p.items():
        for b, y in q.items():
            dst[a+b] += x*y*scale

def permanent_poly(matrix):
    n=len(matrix)
    states=[None]*(1<<n)
    states[0]={0:1}
    for mask in range((1<<n)-1):
        p=states[mask]
        if p is None: continue
        i=mask.bit_count()
        for j in range(n):
            if mask>>j&1: continue
            target=mask|(1<<j)
            if states[target] is None: states[target]=defaultdict(int)
            polyaddprod(states[target],p,matrix[i][j])
        states[mask]=None  # The subset DAG has no edges to an earlier mask.
    return states[-1]

def defect(n):
    base=2*n+1
    u=[base**j for j in range(n)]
    mat=[[{u[(j-i)%n]:1} for j in range(n)] for i in range(n)]
    p=permanent_poly(mat)
    g=[]
    for j in range(n):
        g.append(defaultdict(int))
        for i in range(n):g[-1][u[i]+u[(i+j)%n]]+=1
    q=permanent_poly([[g[(j-i)%n] for j in range(n)] for i in range(n)])
    d=defaultdict(int)
    polyaddprod(d,p,p,n**n)
    for k,c in q.items():d[k]-=factorial(n)*c
    return {k:v for k,v in d.items() if v},u,base

def gap_transform(d,u,base,perm):
    n=len(u)
    # perm[k] is original variable whose sorted rank is k.
    d={sum((k//u[j]%base)*u[perm.index(j)] for j in range(n)):v for k,v in d.items()}
    for j in range(n-1,0,-1):
        out=defaultdict(int)
        for k,v in d.items():
            e=k//u[j]%base
            for h in range(e+1):
                out[k-h*u[j]+h*u[j-1]]+=v*comb(e,h)
        d={k:v for k,v in out.items() if v}
    return d

def affine_reps(n):
    from math import gcd
    units=[a for a in range(1,n) if gcd(a,n)==1]
    for p in permutations(range(n)):
        if p[0]!=0: continue
        if any(tuple((a*x)%n for x in p)<p for a in units):continue
        yield p

if __name__=='__main__':
    if not 2 <= len(sys.argv) <= 3:
        raise ValueError('Usage: circ_gap_test.py ORDER [all|one]')
    n=int(sys.argv[1])
    mode=sys.argv[2] if len(sys.argv)>2 else 'one'
    if n < 3 or mode not in {'all', 'one'}:
        raise ValueError('Require order >= 3 and mode all or one.')
    t=time.time()
    d,u,base=defect(n)
    print('DEFECT',n,len(d),'seconds',time.time()-t,flush=True)
    reps=list(affine_reps(n)) if mode=='all' else [tuple(range(n))]
    if mode == 'all':
        units=[a for a in range(1,n) if gcd(a,n)==1]
        covered={tuple((a*x+b)%n for x in p) for p in reps for a in units for b in range(n)}
        if len(reps) != factorial(n)//(n*len(units)) or len(set(reps)) != len(reps) or covered != set(permutations(range(n))):
            raise ArithmeticError('Incomplete affine chamber coverage.')
    if not reps:
        raise ArithmeticError('No chambers were selected.')
    reports=[]
    for r,p in enumerate(reps):
        g=gap_transform(d,u,base,p)
        if not g:
            raise ArithmeticError('Empty transformed polynomial.')
        negative=[(k,v) for k,v in g.items() if v<0]
        minimal=min(g.values())
        report={'permutation':p,'nonzero_terms':len(g),'negative_terms':len(negative),'min_coefficient':minimal}
        if negative:
            report['negative_examples']=[{'exponents':[k//x%base for x in u],'coefficient':v} for k,v in negative[:10]]
        reports.append(report)
        print(json.dumps({'i':r,**report}),flush=True)
        if negative:
            with open(f'circ_gap_n{n}_{mode}_results.json','w') as f:
                json.dump({'status':'failed','n':n,'chambers':reports},f,indent=2)
            raise ArithmeticError('A negative exact coefficient was found.')
    if {tuple(r['permutation']) for r in reports} != set(reps) or len(reports) != len(reps):
        raise ArithmeticError('Incomplete chamber results.')
    with open(f'circ_gap_n{n}_{mode}_results.json','w') as f:
        json.dump({'status':'passed' if mode=='all' else 'sampled','n':n,'defect':'n^n per(C)^2 - n! per(CC^T)','original_nonzero_terms':len(d),'elapsed_seconds':time.time()-t,'chambers':reports},f,indent=2)
