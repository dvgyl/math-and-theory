#!/usr/bin/env python3
"""Independent exact BFS replay of the reduced subcubic core search through14.

The all-order reduction to14 is a separate proved theorem. Nauty geng supplies
isomorphism-free exhaustive graph generation; this checker imports no boundary
or census implementation from the research generator.
"""
import argparse,json,subprocess,time
from pathlib import Path
from collections import deque
P=Path(__file__).resolve().parent

def decode(s):
 v=[c-63 for c in s.strip()];n=v[0];assert n<63
 bits=[]
 for w in v[1:]:bits.extend((w>>k)&1 for k in range(5,-1,-1))
 adj=[[] for _ in range(n)];k=0
 for j in range(1,n):
  for i in range(j):
   if bits[k]:adj[i].append(j);adj[j].append(i)
   k+=1
 return adj

def boundary(adj):
 n=len(adj);D=[]
 for u in range(n):
  row=[-1]*n;row[u]=0;q=deque([u])
  while q:
   a=q.popleft()
   for b in adj[a]:
    if row[b]<0:row[b]=row[a]+1;q.append(b)
  assert min(row)>=0;D.append(row)
 result=[]
 for u in range(n):
  if any(len(adj[u])*D[u][v]>sum(D[w][v] for w in adj[u]) for v in range(n)):result.append(u)
 return result

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--geng',required=True);args=ap.parse_args();start=time.monotonic();rows=[];hits=[]
 expected={6:(10,10),7:(18,0),8:(49,1),9:(115,0),10:(349,1),11:(1011,0),12:(3421,0),13:(11679,0),14:(43418,0)}
 for n in range(6,15):
  proc=subprocess.Popen([args.geng,'-q','-C','-d2','-D3',str(n)],stdout=subprocess.PIPE,stderr=subprocess.PIPE)
  count=good=0
  for s in proc.stdout:
   adj=decode(s);assert len(adj)==n and all(2<=len(a)<=3 for a in adj);count+=1
   B=boundary(adj)
   if len(B)==6:good+=1;hits.append({'graph6':s.decode().strip(),'boundary':B,'order':n})
  err=proc.stderr.read().decode();assert proc.wait()==0,err;assert(count,good)==expected[n]
  rows.append({'order':n,'graphs':count,'boundary6':good});print(n,count,good,flush=True)
 report={'all_passed':True,'total_graphs':sum(r['graphs'] for r in rows),'total_cores':len(hits),'rows':rows,'cores':hits,'seconds':round(time.monotonic()-start,3),'scope':'Independent integer BFS checker, exhaustive nauty2.8.9 generation through14. The separate tight-pair theorem removes all larger orders.'}
 (P/'subcubic_small_core_verification.json').write_text(json.dumps(report,indent=2)+'\n')
if __name__=='__main__':main()
