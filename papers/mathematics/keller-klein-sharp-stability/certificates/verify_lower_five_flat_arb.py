#!/usr/bin/env python3
"""Validated replay of two exact dyadic partitions for the five-flat plateau.

Case B assumes |b2+b3-m|<x and uses its strict-tail consequence A1>=1/2.
Case C has b2/m<=1/8. The third (triangle) case is proved analytically.
This proves the displayed scalar inequalities, not the whole probability
reduction in Lean. External KK and Hollom--Portier inputs are explicit.
"""
from fractions import Fraction as F
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,lzma,sys,time
from flint import arb,ctx
CASE=sys.argv[1] if len(sys.argv)>1 else 'B';assert CASE in ('B','C')
ctx.prec=int(sys.argv[2]) if len(sys.argv)>2 else 128
ROOT=Path(__file__).resolve().parent;PART=ROOT/f'lower_five_flat_pilot_{CASE}.json.xz'
start=time.time()
def A(q):
 if isinstance(q,int):return arb(q)
 return arb(q.numerator)/arb(q.denominator)
def choose_min(xs):return min(xs,key=lambda z:float(z.mid()))
def choose_max(xs):return max(xs,key=lambda z:float(z.mid()))
def Q(t):return (t/arb(2).sqrt()).erfc()/2
def c(t):return (t/arb(2).sqrt()).erf()/2
ZERO=arb(0);ONE=arb(1);LAM=A(F(1,5)).sqrt();H=c(LAM)
PH=[(A(F(1,7)).sqrt(),F(1,2)),(LAM,F(29,64)),(A(F(1,3)).sqrt(),F(3,8)),(A(F(2,3)).sqrt(),F(1,4)),(ONE,F(7,32))]
W0=F(1,5);W1=F(1,4);X0=F(447,1000);X1=F(9,5);U1=F(1) if CASE=='B' else F(1,8)
assert A(X0)<LAM
assert A(F(1,2)/X1**2)<H
assert 1-2*LAM<A(F(1,8))
assert 2-4*LAM<A(F(1,7)).sqrt()

def endpoints(path):
 box=[F(0),F(1)]*4
 for digit in path:
  d=int(digit);assert 0<=d<=7
  axis,bit=divmod(d,2);lo,hi=box[2*axis:2*axis+2];mid=(lo+hi)/2
  box[2*axis+(0 if bit else 1)]=mid
 return box

def verify_box(path):
 box=endpoints(path)
 wl=W0+(W1-W0)*box[0];wh=W0+(W1-W0)*box[1]
 ul,uh=U1*box[2],U1*box[3];vl,vh=box[4:6]
 xl0=X0+(X1-X0)*box[6];xh0=X0+(X1-X0)*box[7]
 ml,mh=A(wl).sqrt(),A(wh).sqrt();xl,xh=A(xl0),A(xh0)
 Vlo=1-wh*(1+uh*uh*(1+vh*vh));Vhi=1-wl*(1+ul*ul*(1+vl*vl))
 assert Vlo>=F(1,4) and Vhi>0
 sl,sh=A(Vlo).sqrt(),A(Vhi).sqrt()
 Cp=c(ONE) if wh*uh*uh*vh*vh>=Vlo else c(mh*A(uh*vh)/sl)
 al,ah=ul*(1+vl)-1,uh*(1+vh)-1
 abslo=F(0) if al<=0<=ah else min(abs(al),abs(ah));abshi=max(abs(al),abs(ah))
 qs=[(ml*A(1+ul*(1+vl)),mh*A(1+uh*(1+vh))),
 (ml*A(abslo),mh*A(abshi)),
 (ml*A(1-uh*(1-vl)),mh*A(1-ul*(1-vh))),
 (ml*A(1+ul*(1-vh)),mh*A(1+uh*(1-vl)))]
 def T(t):
  assert t>0
  options=[A(F(1,2)),1/(2*t*t),(-t*t/2).exp(),Q(t)+Cp]
  if t>1:options.append(A(F(1,4)))
  return choose_min(options)
 total=ZERO
 for j,(ql,qh) in enumerate(qs):
  num=qh-xl
  umax=num/sh if num<0 else abs(num)/sl
  vmin=(ql+xl)/sh
  qu=Q(umax);Aoptions=[ZERO,qu-Cp]
  if umax<0:Aoptions.append(1-T(-umax))
  for endpoint,p in PH:
   if umax<endpoint:Aoptions.append(A(p/2))
  if CASE=='B' and j==1:Aoptions.append(A(F(1,2)))
  lowA=choose_max(Aoptions)
  lowH=choose_max([ZERO,lowA-T(vmin),qu-Q(vmin)-2*Cp])
  total+=lowH
 upper=choose_min([c(mh),c(xh)-total/8,1/(2*xl*xl)-Q(xh)])
 return H-upper

PART_BYTES=lzma.decompress(PART.read_bytes());p=json.loads(PART_BYTES);assert p['case']==CASE and p['status']=='floating pilot closed' and not p['queue']
paths=[row[0] for row in p['leaves']];assert len(paths)==len(set(paths));trie={}
for path in paths:
 node=trie
 for digit in path:
  assert 'leaf' not in node
  node=node.setdefault(digit,{})
 assert not node
 node['leaf']=True
stack=[trie];internal=0
while stack:
 node=stack.pop()
 if 'leaf' in node:
  assert set(node)=={'leaf'};continue
 keys=sorted(map(int,node));assert len(keys)==2 and keys[0]%2==0 and keys[1]==keys[0]+1
 internal+=1;stack.extend(node.values())
assert internal+1==len(paths)
assert sum((F(1,2**len(path)) for path in paths),F(0))==1
records=[];fail=[]
for i,path in enumerate(paths):
 margin=verify_box(path)
 if not margin>0:fail.append({'path':path,'margin':str(margin)})
 records.append({'path':path,'positive_margin':str(margin)})
 if (i+1)%2000==0:print('verified',i+1,'of',len(paths),'failures',len(fail),flush=True)
result={'status':'PASS' if not fail else 'FAIL','case':CASE,'precision_bits':ctx.prec,
 'verified_at_utc':datetime.now(timezone.utc).isoformat(),'seconds':time.time()-start,
 'leaf_boxes':len(paths),'internal_nodes':internal,'coverage':'Exact dyadic prefix tree, complete binary bisections, total normalized volume one',
 'domain':{'m_squared':[str(W0),str(W1)],'b2':f'm*u, 0<=u<={U1}','b3':'m*u*v, 0<=v<=1','x':[str(X0),str(X1)],'hypothesis':'|b2+b3-m|<x' if CASE=='B' else 'b2/m<=1/8'},
 'conclusion':'The stated four-shift lower-discrepancy envelope is strictly less than c(1/sqrt(5)) on the entire relevant domain.',
 'scalar_checks':{'447/1000<lambda5':str(LAM-A(X0)),'tail_x_ge_9/5':str(H-A(F(1,2)/X1**2)),'1-2lambda5<1/8':str(A(F(1,8))-1+2*LAM),'triangle_threshold_below_1/sqrt7':str(A(F(1,7)).sqrt()-2+4*LAM)},
 'partition_file':PART.name,'partition_sha256':hashlib.sha256(PART_BYTES).hexdigest(),
 'verifier_file':Path(__file__).name,'verifier_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
 'failures':fail,'records':records,
 'scope':'Validated real interval scalar certificate; not an end-to-end Lean proof. Uses python-flint/Arb for sqrt, erf/erfc and exp. The mathematical reduction, analytic triangle case and external inputs are separate.'}
out=ROOT/f'lower_five_flat_{CASE}_arb_{ctx.prec}.json';out.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='records'},indent=2))
if fail:raise SystemExit(1)
