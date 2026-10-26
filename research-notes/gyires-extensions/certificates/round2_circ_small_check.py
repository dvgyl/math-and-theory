#!/usr/bin/env python3
"""Direct independent subset-DP checks of the sparse transfer construction."""
from circ_gap_test import permanent_poly,polyaddprod,gap_transform
from round2_circ_transfer import transfer,advance,identity,trace
from collections import defaultdict
from itertools import permutations
from math import factorial
import json

base=21;u=[base**j for j in range(3)]
aa,bb,cc=[{x:1} for x in u]
d={2*x:1 for x in u};e={u[0]+u[1]:1,u[1]+u[2]:1};f={u[0]+u[2]:1}
Ce=transfer([aa,bb,cc]);Ge=transfer([f,e,d,e,f]);Cp=identity(4);Gp=identity(16)
results=[]
for n in range(1,8):
    Cp=advance(Cp,Ce);Gp=advance(Gp,Ge)
    weights=[defaultdict(int) for _ in range(n)]
    for index,poly in ((-1,aa),(0,bb),(1,cc)):
        for k,v in poly.items():weights[index%n][k]+=v
    p=permanent_poly([[weights[(j-i)%n] for j in range(n)] for i in range(n)])
    gs=[]
    for s in range(n):
        g=defaultdict(int)
        for j in range(n):polyaddprod(g,weights[j],weights[(j+s)%n])
        gs.append(g)
    q=permanent_poly([[gs[(j-i)%n] for j in range(n)] for i in range(n)])
    result={'n':n,'permanent_transfer_matches':dict(p)==dict(trace(Cp)),'gram_transfer_matches':dict(q)==dict(trace(Gp))}
    if n in (3,4):
        D=defaultdict(int);polyaddprod(D,p,p,n**n)
        for k,v in q.items():D[k]-=factorial(n)*v
        D={k:v for k,v in D.items() if v}
        result['chambers']=[]
        for order in permutations(range(3)):
            gap=gap_transform(D,u,base,order)
            result['chambers'].append({'order':order,'min_positive':min(gap.values()),'negative_count':sum(v<0 for v in gap.values()),'nonzero_terms':len(gap)})
            assert all(v>=0 for v in gap.values())
    print(json.dumps(result),flush=True);results.append(result)
    assert result['permanent_transfer_matches'] and result['gram_transfer_matches']
with open('round2_circ_small_check.json','w') as h:json.dump(results,h,indent=2)
