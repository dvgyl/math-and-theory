import json,itertools
from fractions import Fraction
from math import isqrt
from pathlib import Path
x=json.loads((Path(__file__).resolve().parent / 'resolution_witness.json').read_text())
nodes=x['nodes']; weights=[];heights=[];leaves=[]
formula=list(itertools.product([1,-1],repeat=3))
for i,v in enumerate(nodes):
 c=tuple(v['clause']);assert len(c)==3 and set(c)<=set([-1,0,1])
 if 'leaf' in v:
  assert c==formula[v['leaf']]
  w=[Fraction(0)]*8;w[v['leaf']]=Fraction(1);h=0;cnt=1
 else:
  a,b=v['children'];assert 0<=a<i and 0<=b<i
  A=nodes[a]['clause'];B=nodes[b]['clause']
  piv=[j for j in range(3) if A[j]*B[j]==-1];assert len(piv)==1
  r=tuple(0 if j==piv[0] else A[j] or B[j] for j in range(3));assert r==c
  w=[(u+v)/2 for u,v in zip(weights[a],weights[b])];h=1+max(heights[a],heights[b]);cnt=leaves[a]+leaves[b]
 assert sum(w)==1
 weights.append(w);heights.append(h);leaves.append(cnt)
r=x['root'];assert tuple(nodes[r]['clause'])==(0,0,0)
for signs in formula:assert any(all(cj*sj==-1 for cj,sj in zip(c,signs)) for c in formula)
p=weights[r];D=1000
uppers=[Fraction(isqrt((q.numerator*D*D)//q.denominator)+1,D) for q in p]
assert all(u*u>q for u,q in zip(uppers,p))
S=sum(uppers)
# A simple exact gap: certificate exceeds 61/25=2.44 and 1+sqrt2 < 121/50=2.42.
assert Fraction(4)>Fraction(61,25)*S
assert Fraction(71,50)**2>2
out={'valid_nodes':len(nodes),'tree_height':heights[r],'expanded_leaves':leaves[r], 'mass':[str(q) for q in p], 'sqrt_upper_sum':str(S),'certificate_strict_lower':'61/25','conjectured_bound_strict_upper':'121/50'}
print(json.dumps(out,indent=2));(Path(__file__).resolve().parent / 'exact_audit_output.json').write_text(json.dumps(out,indent=2)+'\n')
