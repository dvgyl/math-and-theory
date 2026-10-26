from fractions import Fraction as Q
from itertools import combinations, product
from math import prod
import json, platform

class Hofstadter:
    def __init__(self,k): self.k,self.values=k,[0]
    def __call__(self,n):
        while len(self.values)<=n:
            index=len(self.values)
            value=index-1
            for _ in range(self.k): value=self.values[value]
            self.values.append(index-value)
        return self.values[n]
    def iterate(self,j,n):
        for _ in range(j): n=self(n)
        return n
    def L(self,n): return n+self.iterate(self.k-1,n)
    def iterate_L(self,j,n):
        for _ in range(j): n=self.L(n)
        return n

def hofstadter():
    f4,f5=Hofstadter(4),Hofstadter(5)
    assert (f4.iterate(9,132),f5.iterate(10,132)) == (8,7)
    assert (f4.iterate(9,36),f5.iterate(10,36)) == (2,3)
    rows=[]
    for k in list(range(4,31))+[50,100]:
        f,g=Hofstadter(k),Hofstadter(k+1)
        p=k+3
        A=f.iterate_L(2*k+1,p)
        B=g.iterate_L(2*k+2,p)
        left,right=f.iterate(2*k+1,B),g.iterate(2*k+2,B)
        assert B-A==k-3 and left>p and right==p
        rows.append({'k':k,'A':A,'B':B,'left':left,'right':right})
    return {'finite_witnesses':{'n132':[8,7],'n36':[2,3]},'family_samples':rows}

print(json.dumps({"python":platform.python_version(),"checks":hofstadter(),"status":"PASS","limitation":"Finite checks do not prove universal statements."},indent=2))
