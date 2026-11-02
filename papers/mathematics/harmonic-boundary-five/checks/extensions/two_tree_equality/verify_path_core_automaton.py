#!/usr/bin/env python3
"""Independently reconstruct and certify the complete 18-state automaton.
Uses the three explicit final edge multiplicities of each triangle.
No import of the generator or shortest-path algorithm.
"""
from pathlib import Path
from collections import deque
from itertools import product
import json

ROOT=Path(__file__).resolve().parent

def triangle_requirement(edge):
 result=[]
 for u in range(3):
  a,b=[v for v in range(3) if v!=u]
  r=2+max(edge[u][a],edge[u][b])
  if edge[a][b]>=2:r=max(r,2+edge[u][a]+edge[u][b])
  result.append(r)
 return result

def state(ds,rs,t):
 a,b=sorted(zip(ds,[min(7,x) for x in rs]))
 return (*a,*b,t)

def sign(d,r):
 return (1 if d<r else -1) if ((3<=d<=4 and d<r) or (5<=d<=6 and d>=r)) else None

def initial():
 result=[]
 for a,b,c in product(range(7),repeat=3):
  ds=[2+a+b,2+a+c,2+b+c]
  if ds[1]>=6 or ds[2]>=6:continue
  edge=[[0,1+a,1+b],[1+a,0,2+c],[1+b,2+c,0]]
  rs=triangle_requirement(edge);sg=sign(ds[0],rs[0])
  if sg is not None:result.append((state(ds[1:],rs[1:],2+c),a+b+c+sg,(a,b,c)))
 return result

def successors(s):
 d0,r0,d1,r1,t=s
 outgoing=[];terminal=[]
 for a,b in product(range(7),repeat=2):
  ds=[d0+1+a,d1+1+b,2+a+b]
  if max(ds)>6:continue
  for live in [None,(0,2),(1,2)]:
   t0=1+a+(live==(0,2));t1=1+b+(live==(1,2))
   rs=triangle_requirement([[0,t,t0],[t,0,t1],[t0,t1,0]])
   rs[0]=max(rs[0],r0);rs[1]=max(rs[1],r1)
   if live is None:
    signs=[sign(ds[i],rs[i]) for i in range(3)]
    if None not in signs:terminal.append((s,a+b+sum(signs),(a,b)))
   else:
    dead=1 if live==(0,2) else 0
    sg=sign(ds[dead],rs[dead])
    if sg is None or max(ds[i] for i in live)>=6:continue
    dest=state([ds[i] for i in live],[rs[i] for i in live],t0 if dead==1 else t1)
    outgoing.append((s,dest,a+b+sg,(a,b,1 if dead==1 else 2)))
 return outgoing,terminal

def freeze(x):return tuple(freeze(v) if isinstance(v,list) else v for v in x)

def main():
 c=json.loads((ROOT/'path_core_automaton.json').read_text())
 states={tuple(x['state']) for x in c['potentials']};assert len(states)==18
 init=initial();edges=[];ends=[]
 for s in states:
  e,f=successors(s);edges+=e;ends+=f
  assert all(t in states for _,t,_,_ in e)
 assert len(init)==13 and len(edges)==58 and len(ends)==31
 seen={s for s,w,g in init};assert seen<=states
 while True:
  new=seen|{t for s,t,w,g in edges if s in seen}
  if new==seen:break
  seen=new
 assert seen==states
 p={tuple(x['state']):x['from_source'] for x in c['potentials']}
 q={tuple(x['state']):x['to_sink'] for x in c['potentials']}
 assert all(p[s]<=w for s,w,g in init)
 assert all(p[t]<=p[s]+w and q[s]<=w+q[t] for s,t,w,g in edges)
 assert all(q[s]<=w for s,w,g in ends)
 assert all(p[s]+q[s]>=4 for s in states)
 goodS={s for s in states if p[s]+q[s]==4}
 goodI={x for x in init if x[1]+q[x[0]]==4}
 goodE={x for x in edges if p[x[0]]+x[2]+q[x[1]]==4}
 goodF={x for x in ends if p[x[0]]+x[1]==4}
 assert goodS=={tuple(x) for x in c['optimal_states']}
 assert goodI=={freeze(x) for x in c['optimal_initial']}
 assert goodE=={freeze(x) for x in c['optimal_edges']}
 assert goodF=={freeze(x) for x in c['optimal_terminal']}
 assert len(goodS)==4 and len(goodE)==4
 s=(2,5,3,4,2);assert any(x[0]==s and x[1]==2 for x in goodI) and any(x[0]==s and x[1]==2 for x in goodF)
 # Compare every even extremizer from the independent full ear census.
 import sys
 for base in ROOT.parents:
  for candidate in [base/'literature',base/'five_boundary_research/literature']:
   if (candidate/'verify_sp_delta1_independent.py').is_file():
    sys.path.insert(0,str(candidate));break
  else:continue
  break
 else:raise FileNotFoundError('Cannot locate literature/verify_sp_delta1_independent.py in the research bundle')
 from verify_sp_delta1_independent import tree_code,unique_coloring,decode_graph6,boundary
 def code(adj):return tree_code(adj,unique_coloring(adj))
 def family(r,ends):
  n=2*r+4;adj=[0]*n
  def add(a,b):adj[a]|=1<<b;adj[b]|=1<<a
  for j in range(r-1):add(j,j+1)
  for j in range(r):
   for k in range(max(0,j-1),min(r,j+2)):add(r+j,k)
  for j,kind in zip([0,r-1],ends):
   off=0 if j==0 else 2;p0=2*r+off;q0=p0+1;c0=r+j
   add(p0,j);add(p0,c0);add(q0,j);add(q0,p0 if kind=='P' else c0)
  return tuple(adj)
 census=json.loads((ROOT/'extremizers.json').read_text());compared={}
 for n in [8,10,12,14]:
  r=(n-4)//2;families=[family(r,e) for e in ['PP','PF','FF']]
  assert all(sum(v>0 for v in boundary(g))==n//2+2 for g in families)
  exact={code(decode_graph6(x['graph6'].encode())) for x in census if x['n']==n}
  assert exact=={code(g) for g in families} and len(exact)==3
  compared[n]=3
 result=dict(passed=True,independently_reconstructed_states=18,initial_transitions=13,ordinary_transitions=58,terminal_transitions=31,all_potential_inequalities_verified=True,minimum_weight=4,optimal_states=4,optimal_edges=4,even_census_family_matches=compared,scope='The finite automaton and exact census comparison are checked. The graph-to-pruned-path reduction and state semantics are mathematical proofs in even_equality_classification.md.')
 (ROOT/'path_core_independent_verification.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
