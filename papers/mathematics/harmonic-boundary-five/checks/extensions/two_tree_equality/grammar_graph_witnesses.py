#!/usr/bin/env python3
"""Construct actual graphs for grammar productivity proofs; audit by fresh BFS.
This module does not import the state-transition generator.
"""
from pathlib import Path
from functools import lru_cache
from collections import deque
import json
ROOT=Path(__file__).resolve().parent

def freeze(x):return tuple(freeze(y) if isinstance(y,list) else y for y in x)
def edge(a,b):return (min(a,b),max(a,b))
def neighbors(g):
 n,es,roots=g;adj=[set() for _ in range(n)]
 for a,b in es:adj[a].add(b);adj[b].add(a)
 return adj

def append_ears(n,es,u,v,q):
 es=set(es)
 for _ in range(q):es.add(edge(n,u));es.add(edge(n,v));n+=1
 return n,es

def reverse_roots(g,side):return (g[0],g[1],g[2] if side==0 else g[2][::-1])

def join(g,h,kind):
 n,es,(u,v)=g;m,fs,(a,b)=h
 mapping={b:v} if kind=='triangle' else {a:u,b:v}
 for x in range(m):
  if x not in mapping:mapping[x]=n;n+=1
 es=set(es)|{edge(mapping[x],mapping[y]) for x,y in fs}
 if kind=='triangle':es.add(edge(u,mapping[a]));return (n,frozenset(es),(u,mapping[a])),v
 return (n,frozenset(es),(u,v)),None

def root_state(g):
 n,es,(u,v)=g;adj=neighbors(g)
 t={edge(a,b):len(adj[a]&adj[b]) for a,b in es}
 def one(a,b):
  A=0;B=2
  for w in adj[a]-{b}:A=max(A,2+t[edge(a,w)])
  for x in adj[a]:
   for y in adj[a]:
    if x>=y or y not in adj[x]:continue
    if b in (x,y):
     w=y if x==b else x
     if t[edge(b,w)]>=2:B=max(B,2+t[edge(a,w)])
    elif t[edge(x,y)]>=2:A=max(A,2+t[edge(a,x)]+t[edge(a,y)])
  return (len(adj[a]),min(A,9),min(B,7))
 a,b=one(u,v),one(v,u);s=(t[edge(u,v)],*min(a,b),*max(a,b))
 if a>b:g=(n,es,(v,u))
 return s,g

def make(tag,children):
 kind=tag[0]
 if kind=='leaf':
  _,a,b=tag;n=3;es={(0,1),(0,2),(1,2)}
  n,es=append_ears(n,es,0,1,a);n,es=append_ears(n,es,0,2,b)
  g=(n,frozenset(es),(1,2))
 elif kind=='extend':
  _,side,q0,q1,sg,degree=tag;g=reverse_roots(children[0],side);n,es,(u,v)=g
  n,es=append_ears(n,es,u,v,q0);w=n;n+=1;es.update({edge(w,u),edge(w,v)})
  n,es=append_ears(n,es,v,w,q1);g=(n,frozenset(es),(u,w))
  assert len(neighbors(g)[v])==degree
 elif kind=='triangle':
  _,side1,side2,q1,q2,sg,degree=tag
  g,w=join(reverse_roots(children[0],side1),reverse_roots(children[1],side2),'triangle')
  n,es,(u,v)=g;n,es=append_ears(n,es,u,w,q1);n,es=append_ears(n,es,v,w,q2)
  g=(n,frozenset(es),(u,v));assert len(neighbors(g)[w])==degree
 elif kind=='edge':
  _,side1,side2=tag;g,_=join(reverse_roots(children[0],side1),reverse_roots(children[1],side2),'edge')
 else:raise ValueError(tag)
 return root_state(g)

def scores(g):
 adj=neighbors(g);n=len(adj);ds=[]
 for s in range(n):
  d=[-1]*n;d[s]=0;q=deque([s])
  while q:
   u=q.popleft()
   for v in adj[u]:
    if d[v]<0:d[v]=d[u]+1;q.append(v)
  assert min(d)==0;ds.append(d)
 return [max(sum(ds[u][t]-ds[v][t] for v in adj[u]) for t in range(n)) for u in range(n)]

def component_weight(g):
 n,es,(u,v)=g;h=(n+1,es|{edge(n,u),edge(n,v)},(u,v));beta=scores(h)
 return sum(1 if beta[x]>0 else -1 for x in range(n) if x not in (u,v)),beta

def finish(tag,children):
 _,side1,side2,q,su,sv,du,dv=tag
 g,_=join(reverse_roots(children[0],side1),reverse_roots(children[1],side2),'edge')
 n,es,(u,v)=g;n,es=append_ears(n,es,u,v,q);g=(n,frozenset(es),(u,v))
 adj=neighbors(g);assert len(adj[u])==du and len(adj[v])==dv
 return g

def main():
 a=json.loads((ROOT/'extremal_grammars.json').read_text())
 mu={(x['leaves'],tuple(x['state'])):x['minimum_weight'] for x in a['all_minimum_potentials']}
 cert={freeze(x['state']):x for x in a['productivity_certificates']}
 @lru_cache(None)
 def witness(key):
  row=cert[key];dest,children,w,tag,red=freeze(row['rule'])
  assert dest==key and all(cert[c]['rank']<row['rank'] for c in children)
  s,g=make(tag,[witness(c) for c in children]);assert s==key[1]
  return g
 maxn=0
 for key,row in sorted(cert.items(),key=lambda item:item[1]['rank']):
  g=witness(key);maxn=max(maxn,g[0]);actual,_=component_weight(g)
  assert actual==mu[key[:2]]+key[2],(key,actual,mu[key[:2]]+key[2])
 print('Productivity witnesses:',len(cert),'max order',maxn,flush=True)
 audit={}
 for target in ['4','5']:
  data=a['targets'][target];rule_count=0;final_count=0
  for dest,children,w,tag,red in map(freeze,data['rules']):
   s,g=make(tag,[witness(c) for c in children]);assert s==dest[1]
   actual,_=component_weight(g);assert actual==mu[dest[:2]]+dest[2]
   rule_count+=1
  finals=[]
  for left,right,w,tag in map(freeze,data['final_rules']):
   g=finish(tag,[witness(left),witness(right)]);beta=scores(g);b=sum(x>0 for x in beta);i=g[0]-b
   assert b-i==int(target) and b==(g[0]+1)//2+2
   final_count+=1;finals.append(dict(n=g[0],boundary=b,edges=sorted(g[1])))
  audit[target]=dict(rules=rule_count,terminal_choices=final_count,all_graph_witnesses_pass=True)
  (ROOT/f'target{target}_terminal_graph_witnesses.json').write_text(json.dumps(finals,separators=(',',':'))+'\n')
 result=dict(passed=True,productivity_graph_witnesses=len(cert),maximum_witness_order=maxn,targets=audit,method='Actual graph construction from every productivity proof and every accepted production/terminal choice; fresh all-pairs BFS scores, independent of transition arithmetic.')
 (ROOT/'grammar_graph_witness_verification.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
