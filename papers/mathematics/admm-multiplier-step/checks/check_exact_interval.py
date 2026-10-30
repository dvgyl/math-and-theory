"""Independent standard-library audit of an ADMM interval certificate.

No NumPy, SDP solver, Sympy, floating-point arithmetic, or input tolerances are
used. This checks the rational data behind the mathematical Lyapunov proof;
it is not a substitute for the requested Lean verification of that proof.
"""
import argparse
from fractions import Fraction as Q
import json
from pathlib import Path


def zeros(n,m=None):return [[Q(0) for _ in range(n if m is None else m)] for _ in range(n)]
def transpose(A):return list(map(list,zip(*A)))
def multiply(A,B):
    return [[sum((a*b for a,b in zip(row,col)),Q(0)) for col in zip(*B)] for row in A]
def subtract(A,B):return [[a-b for a,b in zip(x,y)] for x,y in zip(A,B)]
def vector_sub(a,b):return [x-y for x,y in zip(a,b)]
def vector_add(a,b):return [x+y for x,y in zip(a,b)]
def scale_vector(t,a):return [t*x for x in a]
def symmetric_outer(a,b):
    return [[(a[i]*b[j]+b[i]*a[j])/2 for j in range(len(a))] for i in range(len(a))]
def parse_matrix(A):return [[Q(x) for x in row] for row in A]


def check_ldl(A,Lraw,draw):
    n=len(A);L=parse_matrix(Lraw);d=list(map(Q,draw));D=zeros(n)
    assert len(L)==len(d)==n
    assert all(len(row)==n for row in L)
    assert A==transpose(A)
    for i in range(n):
        assert d[i]>0
        D[i][i]=d[i]
        assert L[i][i]==1
        assert all(L[i][j]==0 for j in range(i+1,n))
    assert multiply(multiply(L,D),transpose(L))==A


def check(path):
    data=json.loads(Path(path).read_text())
    assert data['pure_quadratic'] is True
    m=data['memory'];n=2*(m+1);p=2*m
    lam=list(map(Q,data['multipliers']))
    inds=data['interpolation_indices']
    assert len(lam)==len(inds)==2*m*(m+1)
    assert all(x>=0 for x in lam)
    expected={(name,i,j) for name in ('f','g') for i in range(m+1)
              for j in range(m+1) if i!=j}
    assert {(r['name'],r['i'],r['j']) for r in inds}==expected
    for name in ('f','g'):
        flow=[Q(0)]*(m+1)
        for weight,row in zip(lam,inds):
            if row['name']==name:
                flow[row['i']]-=weight;flow[row['j']]+=weight
        assert flow==[0]*(m+1)
    endpoints=list(map(Q,data['interval']))
    assert len(data['endpoints'])==len(endpoints)
    assert len(endpoints) in (1,2)
    assert all(t>0 for t in endpoints)
    if len(endpoints)==2:assert endpoints[0]<endpoints[1]
    E=zeros(n)
    for i in range(n):E[i][i]=1
    Z=E[::2];V=E[1::2];zero=[Q(0)]*n
    D=[vector_sub(E[i+2],E[i]) for i in range(p)]
    diss=zeros(n)
    for diff in (vector_sub(Z[m],Z[m-1]),vector_sub(V[m],V[m-1])):
        term=symmetric_outer(diff,diff)
        diss=[[a+b for a,b in zip(x,y)] for x,y in zip(diss,term)]
    for endpoint,tau in zip(data['endpoints'],endpoints):
        assert Q(endpoint['tau'])==tau
        X=[zero]+[vector_add(Z[j],vector_sub(V[j],V[j-1])) for j in range(1,m+1)]
        A=[zero]+[vector_sub(vector_sub(Z[j-1],scale_vector(tau,V[j-1])),X[j])
                  for j in range(1,m+1)]
        B=[zero]+[vector_sub(vector_add(X[j],scale_vector(tau,V[j-1])),Z[j])
                  for j in range(1,m+1)]
        points={'f':X,'g':[zero]+Z[1:]};grads={'f':A,'g':B}
        Qsum=zeros(n)
        for weight,row in zip(lam,inds):
            name=row['name'];i=row['i'];j=row['j']
            term=symmetric_outer(grads[name][i],vector_sub(points[name][j],points[name][i]))
            # The interpolation expression is f_j-f_i-<a_i,x_j-x_i>.
            Qsum=[[a-weight*b for a,b in zip(x,y)] for x,y in zip(Qsum,term)]
        P=parse_matrix(endpoint['P']);T=parse_matrix(endpoint['T'])
        assert len(P)==len(T)==p and all(len(row)==p for row in P+T)
        assert P==transpose(P)
        M=zeros(n)
        for i in range(p):
            for j in range(p):
                M[i][j]+=P[i][j];M[i+2][j+2]-=P[i][j]
        M=subtract(subtract(M,diss),Qsum)
        assert M==multiply(multiply(transpose(D),T),D)
        lower=[row[:] for row in P]
        lower[p-2][p-2]-=1;lower[p-1][p-1]-=1
        assert lower==parse_matrix(endpoint['lower'])
        check_ldl(T,endpoint['T_LDL_L'],endpoint['T_LDL_D'])
        check_ldl(lower,endpoint['lower_LDL_L'],endpoint['lower_LDL_D'])
        print(f'PASS endpoint tau={tau}: exact decrease identity and positive LDL certificates.')
    print(f'PASS: {len(lam)} nonnegative multipliers with exact f/g flow balance; memory={m}.')
    if len(endpoints)==2:
        print(f'Both affine endpoints checked: [{endpoints[0]}, {endpoints[1]}].')
    print('No floating-point arithmetic or numerical feasibility tolerance used.')


if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('certificate',nargs='?',default=str(Path(__file__).with_name('exact_16_18_m6.json')))
    check(parser.parse_args().certificate)
