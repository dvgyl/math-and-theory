#!/usr/bin/env python3
"""Standalone exhaustive integer check of genuine polymatroid witnesses.
All32 overlaps, all pairs of subsets for submodularity, all comparable
subset pairs for monotonicity. No LP/search/scientific-library imports.
"""
from pathlib import Path
from itertools import combinations
import argparse,json,hashlib

def cis(n):
 for i,j in combinations(range(n),2):
  remaining=[k for k in range(n) if k not in (i,j)]
  for size in range(n-1):
   for K in combinations(remaining,size):yield i,j,sum(1<<k for k in K)

def verify(path):
 raw=Path(path).read_bytes();doc=json.loads(raw)
 assert doc['n']==5
 pattern=doc['pattern'];assert len(pattern)==80 and set(pattern)<=set('01')
 assert pattern=='01111101110000011101001111010011011111010111111101111110111101011111010101100101'
 lam=doc['common_modular_offset'];assert isinstance(lam,int) and lam>=0
 seen=set();pairs_total=0;monotone_total=0;rows=[]
 for w in doc['certificates']:
  L=w['overlap'];assert 0<=L<32 and L not in seen;seen.add(L)
  dim=w['ground_size'];copy=w['copy_map'];m=w['standardized_supermodular_values']
  assert dim==10-L.bit_count() and len(m)==1<<dim and all(isinstance(x,int) for x in m)
  assert len(copy)==5 and len(set(copy))==5
  assert all(copy[i]==i if L>>i&1 else copy[i]>=5 for i in range(5))
  assert set(copy)|set(range(5))==set(range(dim))
  M=sum(1<<i for i in copy);assert M&31==L
  assert m[0]==0 and all(m[1<<i]==0 for i in range(dim))
  h=[lam*S.bit_count()-value for S,value in enumerate(m)]
  assert h[0]==0
  count=len(h);pairs=0;mono=0
  for A in range(count):
   # Every B subset A, including B=A and the empty subset.
   B=A
   while True:
    assert h[B]<=h[A],('monotonicity',L,A,B,h[A],h[B]);mono+=1
    if B==0:break
    B=(B-1)&A
   for B in range(A,count):
    assert h[A]+h[B]>=h[A|B]+h[A&B],('submodularity',L,A,B);pairs+=1
  for S in range(32):
   copied=sum(1<<copy[i] for i in range(5) if S>>i&1)
   assert h[S]==h[copied],('copy restriction',L,S)
  nonzero=[]
  for char,(i,j,K) in zip(pattern,cis(5)):
   d=h[K|(1<<i)]+h[K|(1<<j)]-h[K]-h[K|(1<<i)|(1<<j)]
   assert (d==0)==(char=='0'),('CI pattern',L,i,j,K,d)
   assert d>=0
   if d>0:nonzero.append(d)
  U=count-1
  assert h[31]+h[M]-h[U]-h[L]==0,('group CI',L)
  rows.append({'overlap':L,'ground_size':dim,'submodular_pairs_checked':pairs,'monotone_pairs_checked':mono,'positive_CMI_minimum':min(nonzero),'integer_polymatroid_verified':True})
  pairs_total+=pairs;monotone_total+=mono
 assert seen==set(range(32))
 return {'exact_integer_polymatroid_check':'PASS','n':5,'pattern':pattern,'overlaps_checked':32,'common_modular_offset':lam,'all_subset_pairs_checked':pairs_total,'all_comparable_pairs_checked':monotone_total,'certificate_sha256':hashlib.sha256(raw).hexdigest(),'checks':rows,'structural_selfadhesivity_all_overlaps':True,'single_common_base_asserted':False,'Lean_verified':False}

if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('certificate',nargs='?',default='info_a/continuation/E3_all_overlap_polymatroids.json');p.add_argument('--output',default='info_a/continuation/E3_all_overlap_check_results.json');a=p.parse_args()
 r=verify(a.certificate);Path(a.output).write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({k:v for k,v in r.items() if k!='checks'},indent=2))
