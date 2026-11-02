#!/usr/bin/env python3
"""Standard-library exact audit of the infinite six-point metric obstruction."""
from pathlib import Path
from itertools import product
from collections import deque
import json,time
P=Path(__file__).resolve().parent

def metric(t):return [[0 if i==j else (2*t-1 if (i<3)==(j<3) else t) for j in range(6)] for i in range(6)]
def profile(t,i,j,a,b):return tuple([a if h==i else 2*t-1-a for h in range(3)]+[b if h==j else 2*t-1-b for h in range(3)])
def norm(f,g):return max(abs(x-y) for x,y in zip(f,g))
def frame(t):return {(i,j,a,b):profile(t,i,j,a,b) for i,j in product(range(3),repeat=2) for a,b in product(range(1,t),repeat=2) if a+b>=t}
def bfs(N,u):
 d={u:0};q=deque([u])
 while q:
  x=q.popleft()
  for y in N[x]:
   if y not in d:d[y]=d[x]+1;q.append(y)
 return d

def main():
 start=time.monotonic();checks=[]
 for t in range(3,13):
  M=metric(t);F=frame(t)
  assert len(F)==9*t*(t-1)//2
  if t<=5:
   brute={f for f in product(range(1,2*t-1),repeat=6) if all(all(f[i]+f[j]>=M[i][j] for j in range(6)) and any(f[i]+f[j]==M[i][j] for j in range(6)) for i in range(6))}
   assert brute==set(F.values())
  local=[tuple(M[0])]+[F[0,j,1,t-1] for j in range(3)]+[F[0,j,2,t-2] for j in range(3)]
  LN=[[v for v in range(7) if norm(local[u],local[v])==1] for u in range(7)]
  assert len(LN[0])==3 and all(len(LN[u])==4 for u in range(1,4))
  for u in range(4):
   for k in range(6):
    if local[u][k]>0:assert any(local[w][k]==local[u][k]-1 for w in LN[u])
    if u:assert sum(local[u][k]-local[w][k] for w in LN[u])<=0
   for v in range(7):
    if u!=v:assert any(norm(local[w],local[v])==norm(local[u],local[v])-1 for w in LN[u])
    if u:assert sum(norm(local[u],local[v])-norm(local[w],local[v]) for w in LN[u])<=0
  removed=set()
  for k in range(1,t-1):
   for i,j in product(range(3),repeat=2):
    u=F[i,j,k,t-k];target=(i+1)%3
    ns=[z for z,p in F.items() if norm(u,p)==1]
    forced=[z for z in ns if z[2]+z[3]==t]
    forced_boundary=[h for h,row in enumerate(M) if norm(u,row)==1]
    base=sum(u[target]-F[z][target] for z in forced)+sum(u[target]-M[h][target] for h in forced_boundary)
    assert base==0,(t,k,i,j,base)
    optional=[z for z in ns if z not in forced]
    assert all(u[target]-F[z][target]>=0 for z in optional)
    removed.update(z for z in optional if u[target]-F[z][target]>0)
  assert {z for z in F if z[2]+z[3] in (t+1,t+2)}<=removed
  diag=[p for z,p in F.items() if z[2]+z[3]==t];Q=[tuple(r) for r in M]+diag
  N=[[v for v in range(len(Q)) if norm(Q[u],Q[v])==1] for u in range(len(Q))]
  assert len(bfs(N,0))==len(Q)
  a=Q.index(F[0,0,1,t-1]);b=Q.index(F[1,1,t-1,1]);assert norm(Q[a],Q[b])==t-1 and bfs(N,a)[b]==t
  checks.append({'t':t,'positive_profiles':len(F),'local_witness_vertices':7,'diagonal_graph_order':len(Q),'all_checks_passed':True})
 report={'all_passed':True,'full_profile_enumeration_t':[3,4,5],'parameter_checks':checks,'seconds':round(time.monotonic()-start,3),'scope':'Exact finite audit; the all-t theorem has a separate complete mathematical proof.'}
 (P/'infinite_obstruction_verification.json').write_text(json.dumps(report,indent=2)+'\n');print(report)
if __name__=='__main__':main()
