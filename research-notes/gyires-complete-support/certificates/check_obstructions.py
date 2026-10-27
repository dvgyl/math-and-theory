"""Exact checks of failed-proof examples. These do not refute Gyires."""

if not __debug__:
    raise RuntimeError("Certificate checks require assertions. Run Python without -O or PYTHONOPTIMIZE.")

from collections import defaultdict
from fractions import Fraction as F
from itertools import permutations
from math import prod
import json

def per(a):
 n=len(a);return sum(prod(a[i][p[i]] for i in range(n)) for p in permutations(range(n)))
def gram(a):return [[sum(x*y for x,y in zip(r,s)) for s in a] for r in a]
def mul(p,q):
 out=defaultdict(int)
 for a,x in p.items():
  for b,y in q.items():out[tuple(u+v for u,v in zip(a,b))]+=x*y
 return dict(out)
def add(p,q,scale=1):
 out=defaultdict(int,p)
 for k,v in q.items():out[k]+=scale*v
 return {k:v for k,v in out.items() if v}
def polyper(a):
 n=len(a);out={}
 for p in permutations(range(n)):
  term={(0,0,0):1}
  for i in range(n):term=mul(term,a[i][p[i]])
  out=add(out,term)
 return out

def main():
 a=[[F(v,4) for v in row] for row in [[1,1,2],[0,2,2],[3,1,0]]]
 repeated=[[row[j] for j in [0,2,2]] for row in a]
 assert per(a)==F(5,16) and per(repeated)==F(3,8)
 a=[[F(v,2) for v in row] for row in [[1,0,1],[1,1,0],[0,1,1]]]
 b=[[F(v,4) for v in row] for row in [[1,1,2],[2,2,0],[1,1,2]]]
 r0=per(a)**2/per(gram(a));r1=per(b)**2/per(gram(b))
 assert r0==F(1,4) and r1==F(4,15) and r1>r0
 mat=[[{(1,0,0):6,(0,1,0):1,(0,0,1):1} if i==j else {(1,0,0):6,(0,1,0):3} for j in range(4)] for i in range(4)]
 g=[[{} for _ in range(4)] for _ in range(4)]
 for i in range(4):
  for j in range(4):
   for k in range(4):g[i][j]=add(g[i][j],mul(mat[i][k],mat[j][k]))
 p=polyper(mat);d=add({k:256*v for k,v in mul(p,p).items()},polyper(g),-24)
 assert d[(6,1,1)]==-6879707136
 assert d[(6,1,1)]==256*24*2*6**6*(-12)
 S=F(6,31);gamma=1-S/3-F(3,4)*S**2-F(11,4)**4*S**3/(1-F(11,4)*S)
 assert gamma==F(9301,445904) and gamma>0
 result={'status':'PASS','repeated_columns':{'original_permanent':'5/16','repeated_permanent':'3/8'},'row_averaging':{'before':str(r0),'after':str(r1)},'arbitrary_birkhoff_gaps':{'coefficient_t6uv':d[(6,1,1)],'negative_coefficients':sum(v<0 for v in d.values())},'three_row_threshold31_gamma':str(gamma),'interpretation':'No example here refutes Gyires; examples refute stronger intermediate assertions.'}
 print(json.dumps(result,indent=2))
if __name__=='__main__':main()
