#!/usr/bin/env python3
"""Exact rational obstruction certificates; not a proof of general Gyires."""

if not __debug__:
    raise RuntimeError("Certificate checks require assertions. Run Python without -O or PYTHONOPTIMIZE.")

from fractions import Fraction as F
from collections import defaultdict
from pathlib import Path
from math import factorial
import json

def permanent(A):
    values={0:F(1)}
    for row in A:
        nxt=defaultdict(F)
        for mask,value in values.items():
            for j,a in enumerate(row):
                if not mask>>j&1:nxt[mask|1<<j]+=value*a
        values=nxt
    return values[(1<<len(A))-1]

def transpose(A):return list(map(list,zip(*A)))
def multiply(A,B):return [[sum((a*b for a,b in zip(row,col)),F()) for col in zip(*B)] for row in A]
def ratio(A):return permanent(A)**2/permanent(multiply(A,transpose(A)))
def stochastic(A):return all(x>=0 for row in A for x in row) and all(sum(row)==1 for row in A) and all(sum(col)==1 for col in zip(*A))
def complement(A,i,j):
    return [[A[k][l]+A[k][j]*A[i][l]/(1-A[i][j]) for l in range(len(A)) if l!=j] for k in range(len(A)) if k!=i]
def star(n):
    m=n-1
    return [[F(0) if i==j==0 else F(1,m) if i==0 or j==0 else F(m-1,m) if i==j else F(0) for j in range(n)] for i in range(n)]

def main():
    output={'status':'all exact rational assertions passed','scope':'refutes only auxiliary pivot assertions; neither Gyires nor best-pivot induction is refuted','cases':[]}
    for n in [3,6]:
        A=star(n);assert stochastic(A)
        R=ratio(A);g=F(n-1,n)**(n-1);P=permanent(A)
        q={};matching={}
        for i in range(n):
            for j in range(n):
                B=complement(A,i,j);assert stochastic(B)
                q[i,j]=g*ratio(B)/R
                minor=[[A[k][l] for l in range(n) if l!=j] for k in range(n) if k!=i]
                matching[i,j]=A[i][j]*permanent(minor)/P
                assert matching[i,j]==A[i][j]
        positive={q[i,j] for i in range(n) for j in range(n) if A[i][j]>0}
        zero={q[i,j] for i in range(n) for j in range(n) if A[i][j]==0}
        weighted=sum((A[i][j]*q[i,j] for i in range(n) for j in range(n)),F())/n
        if n==3:
            assert positive=={F(8,9)}
            assert zero=={F(200,153)}
        else:
            assert P==F(256,3125)
            assert permanent(multiply(A,transpose(A)))==F(3222392,48828125)
            assert R==F(40960,402799)
            assert positive=={F(10069975,9928008)}
            assert q[0,0]==F(4412398635249631,1254003292274688)
            assert q[1,2]==F(53959742125,81341812224)
            assert weighted==F(10069975,9928008)>1
            assert R>F(factorial(n),n**n)
        output['cases'].append({'n':n,'permanent':str(P),'gram_permanent':str(permanent(multiply(A,transpose(A)))),'R':str(R),'positive_pivot_ratios':sorted(map(str,positive)),'zero_pivot_ratios':sorted(map(str,zero)),'entry_weighted_mean':str(weighted),'matching_marginals_equal_A':True,'best_pivot_ratio':str(min(q.values()))})
    Path('boundary_exact.json').write_text(json.dumps(output,indent=2)+'\n')
    print(json.dumps(output,indent=2))
if __name__=='__main__':main()
