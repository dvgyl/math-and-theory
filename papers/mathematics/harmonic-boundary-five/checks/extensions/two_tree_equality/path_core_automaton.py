#!/usr/bin/env python3
"""Finite weighted automaton for pruned-path-core extremal two-trees.
State: two open-edge endpoints (current degree, final-degree requirement),
and final triangle multiplicity of their open edge. Requirements are capped
at seven since every global degree is at most six. No distances are used.
"""
from collections import deque,defaultdict
from pathlib import Path
import json
CAP=6; BCAP=4

def norm(d1,r1,d2,r2,t):
 a,b=sorted(((d1,min(r1,CAP+1)),(d2,min(r2,CAP+1))))
 return (*a,*b,t)

def requirements(tab,tac,tbc):
 a=max(2+tab,2+tac,2+tab+tac if tbc>=2 else 0)
 b=max(2+tab,2+tbc,2+tab+tbc if tac>=2 else 0)
 c=max(2+tac,2+tbc,2+tac+tbc if tab>=2 else 0)
 return a,b,c

def status(d,r):
 if not 3<=d<=CAP:return None
 if d<r:return 1 if d<=BCAP else None
 return -1 if d>=5 else None

def build():
 init=[]
 # Triangle a,u,v. uv open, au,av closed. a is forgotten.
 for qa in range(CAP-1):
  for qb in range(CAP-1):
   for q in range(CAP-1):
    da=2+qa+qb;du=2+qa+q;dv=2+qb+q
    if max(da,du,dv)>CAP or max(du,dv)>=CAP:continue
    ra,ru,rv=requirements(1+qa,1+qb,2+q)
    sign=status(da,ra)
    if sign is None:continue
    s=norm(du,ru,dv,rv,2+q)
    init.append((s,qa+qb+q+sign,(qa,qb,q)))
 states=set(s for s,w,g in init);todo=deque(states);edges=[];ends=[]
 while todo:
  s=todo.popleft();d1,r1,d2,r2,t=s
  for q1 in range(CAP-1):
   for q2 in range(CAP-1):
    D1=d1+1+q1;D2=d2+1+q2;D3=2+q1+q2
    if max(D1,D2,D3)>CAP:continue
    for cont in [0,1,2]: #0 terminal,1 keep1,new,2 keep2,new
     t1=1+q1+(cont==1);t2=1+q2+(cont==2)
     x1,x2,x3=requirements(t,t1,t2)
     R1=max(r1,x1);R2=max(r2,x2);R3=x3
     if cont==0:
      sig=[status(d,r) for d,r in [(D1,R1),(D2,R2),(D3,R3)]]
      if None not in sig:ends.append((s,q1+q2+sum(sig),(q1,q2)))
     else:
      dd,rr=(D2,R2) if cont==1 else (D1,R1)
      sign=status(dd,rr)
      if sign is None:continue
      liveD,liveR,tt=(D1,R1,t1) if cont==1 else (D2,R2,t2)
      if max(liveD,D3)>=CAP:continue
      dest=norm(liveD,liveR,D3,R3,tt)
      edges.append((s,dest,q1+q2+sign,(q1,q2,cont)))
      if dest not in states:states.add(dest);todo.append(dest)
 return sorted(states),init,edges,ends

def shortest(states,init,edges,ends):
 INF=10**9
 ds={s:INF for s in states}
 for s,w,g in init:ds[s]=min(ds[s],w)
 for _ in range(len(states)):
  change=False
  for s,t,w,g in edges:
   if ds[t]>ds[s]+w:ds[t]=ds[s]+w;change=True
  if not change:break
 else:raise AssertionError('negative cycle')
 dt={s:INF for s in states}
 for s,w,g in ends:dt[s]=min(dt[s],w)
 for _ in range(len(states)):
  change=False
  for s,t,w,g in edges:
   if dt[s]>w+dt[t]:dt[s]=w+dt[t];change=True
  if not change:break
 else:raise AssertionError('negative co-cycle')
 optimum=min(ds[s]+w for s,w,g in ends)
 return optimum,ds,dt

def main():
 states,init,edges,ends=build();opt,ds,dt=shortest(states,init,edges,ends)
 goodS=[s for s in states if ds[s]+dt[s]==opt]
 goodI=[(s,w,g) for s,w,g in init if w+dt[s]==opt]
 goodE=[(s,t,w,g) for s,t,w,g in edges if ds[s]+w+dt[t]==opt]
 goodF=[(s,w,g) for s,w,g in ends if ds[s]+w==opt]
 result=dict(states=len(states),initial_transitions=len(init),transitions=len(edges),terminal_transitions=len(ends),optimum=opt,optimal_states=goodS,optimal_initial=goodI,optimal_edges=goodE,optimal_terminal=goodF,potentials=[dict(state=s,from_source=ds[s],to_sink=dt[s]) for s in states])
 out=Path(__file__).with_name('path_core_automaton.json');out.write_text(json.dumps(result,indent=2)+'\n')
 print({k:v for k,v in result.items() if k!='potentials'})
if __name__=='__main__':main()
