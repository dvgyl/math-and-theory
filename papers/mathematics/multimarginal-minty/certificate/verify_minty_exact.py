"""Exact integer/rational verification of the finite Minty obstructions.

This verifies finite inequalities and a sum-of-squares certificate using
Fraction arithmetic. It does not itself prove the Zorn maximal-extension
theorem; that ordinary/formal obligation is separate.
"""
from fractions import Fraction as F
from itertools import combinations
import json
from pathlib import Path

P=[ [(-1,-2),(3,-12),(9,-2)],
    [(-2,-5),(0,-7),(-14,-2)],
    [(2,0),(-4,15),(14,-1)] ]
S=[tuple(sum(p[i][k] for i in range(3)) for k in range(2)) for p in P]
def dot(a,b):return sum(x*y for x,y in zip(a,b))
def sub(a,b):return tuple(x-y for x,y in zip(a,b))
slacks=[]
for a,b in combinations(range(3),2):
    ds=sub(S[a],S[b]);row=[]
    for i in range(3):
        d=sub(P[a][i],P[b][i]);row.append(dot(d,ds)-dot(d,d))
    assert min(row)>=0;slacks.append({'pair':[a,b],'singleton_slacks':row})

# Polynomial dictionaries in four coordinates a,b,c,d, with w=-u-v.
ZERO=(0,0,0,0)
def add(*ps):
    out={}
    for p in ps:
        for e,v in p.items():out[e]=out.get(e,F(0))+v
    return {e:v for e,v in out.items() if v}
def scale(p,s):return {e:s*v for e,v in p.items() if s*v}
def mul(p,q):
    out={}
    for e,v in p.items():
        for f,w in q.items():
            k=tuple(x+y for x,y in zip(e,f));out[k]=out.get(k,F(0))+v*w
    return {e:v for e,v in out.items() if v}
def const(x):return {ZERO:F(x)} if x else {}
def var(i):e=list(ZERO);e[i]=1;return {tuple(e):F(1)}
a,b,c,d=map(var,range(4));u=[a,b];v=[c,d];w=[scale(add(a,c),-1),scale(add(b,d),-1)]
def norm2(z):return add(*(mul(t,t) for t in z))
qA=add(norm2(u),scale(a,13),scale(b,-12),const(-16))
qBv=add(norm2(v),scale(c,-16),const(-49))
qBw=add(norm2(w),scale(w[0],12),scale(w[1],-10),const(-52))
qC=add(norm2(v),scale(c,20),scale(d,-16),const(79))
lhs=add(scale(qA,4),scale(qBv,3),scale(qBw,4),scale(qC,8))
t1=add(a,scale(c,F(1,2)),const(F(1,4)))
t2=add(b,scale(d,F(1,2)),const(F(-1,2)))
t3=add(c,const(F(31,13)))
t4=add(d,const(F(-42,13)))
rhs=add(scale(mul(t1,t1),8),scale(mul(t2,t2),8),
        scale(mul(t3,t3),13),scale(mul(t4,t4),13),const(F(23,26)))
assert lhs==rhs
assert F(23,26)>0

# Independent check of root's symmetric three-dimensional data.
P3=[];S3=[];C3=[]
for j in range(3):
    s=[48 if k==j else -24 for k in range(3)];S3.append(s)
    p=[]
    for i in range(3):p.append([34 if k==j else 10 for k in range(3)] if i==j else [7 if k==j else -17 for k in range(3)])
    assert [sum(p[i][k] for i in range(3)) for k in range(3)]==s
    P3.append(p);C3.append([p[j][k]-F(s[k],2) for k in range(3)])
root_slacks=[]
for j,k in combinations(range(3),2):
    ds=sub(S3[j],S3[k]);row=[]
    for i in range(3):
        e=sub(P3[j][i],P3[k][i]);row.append(dot(e,ds)-dot(e,e))
    root_slacks.append(row);assert row==[117 if i in [j,k] else 2304 for i in range(3)]
assert [sum(c[k] for c in C3) for k in range(3)]==[54,54,54]
assert all(F(dot(s,s),4)==864 for s in S3)
root_min=F(dot([54,54,54],[54,54,54]),3)-3*864
assert root_min==324

record={'planar_points':P,'planar_sums':S,'planar_slacks':slacks,
        'planar_certificate_minimum':'23/26','polynomial_identity_verified':True,
        'root_3d_slacks':root_slacks,'root_3d_certificate_minimum':str(root_min)}
out=Path(__file__).with_name('minty_exact_verification.json');out.write_text(json.dumps(record,indent=2));print(json.dumps(record,indent=2))
