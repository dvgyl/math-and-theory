import numpy as np
from scipy.optimize import brentq, differential_evolution

def cross(d):
 return np.array([[0,-d[2],d[1]],[d[2],0,-d[0]],[-d[1],d[0],0]])
def orthnull(M,tol=1e-9):
 u,s,v=np.linalg.svd(M,full_matrices=True);r=np.count_nonzero(s>tol)
 return v[r:].T

def boundary(A,d,s,tol=1e-10):
 aa,U=np.linalg.eigh(A);z=U.T@d;top=abs(aa-aa[-1])<tol
 low=~top
 ua=np.zeros(3);ua[low]=z[low]/(aa[-1]-aa[low])
 if np.linalg.norm(z[top])<tol and ua@ua<=1+tol:
  ua[np.flatnonzero(top)[0]]=np.sqrt(max(0,1-ua@ua));u=U@ua
  return s+aa[-1]+z@ua,u
 def sec(mu):return np.sum((z/(mu-aa))**2)-1
 lo=aa[-1]+max(1,abs(aa[-1]))*1e-12;hi=max(lo+1,np.linalg.norm(d)+aa[-1]+1)
 while sec(hi)>0:hi*=2
 mu=brentq(sec,lo,hi,xtol=1e-14);ua=z/(mu-aa);u=U@ua
 return s+mu+z@ua,u

def spec(T,c):
 A=T@T.T;d=T@c;s=c@c;C=cross(d);K=A-s*np.eye(3)
 ka,ku=np.linalg.eigh(K);nsel=abs(ka)<1e-9;Z=ku[:,nsel];Kp=(ku[:,~nsel]/ka[~nsel])@ku[:,~nsel].T
 B=C@Z;U=orthnull(B.T);M=A+C@Kp@C;L=U.T@M@U
 vals,vecs=np.linalg.eigh(L);E,u=boundary(A,d,s);cand=[(E,u,'boundary')]
 groups=[]
 for i,lam in enumerate(vals):
  if any(abs(lam-v[0])<1e-8 for v in groups):continue
  ids=abs(vals-lam)<1e-8;W=U@vecs[:,ids];groups.append((lam,W))
 for lam,W in groups:
  if abs(lam-s)<1e-8:
   ca,cu=np.linalg.eigh(K+1j*C);Q=cu[:,abs(ca)<1e-8]
   if Q.shape[1]==0:raise RuntimeError('missing exceptional kernel')
   z=Q[:,0];zz=z@z
   if abs(zz)>1e-15:z*=np.exp(-.5j*np.angle(zz))
   n=z.real;v=z.imag
   if n@n<v@v:n,v=v,-n
   v=v/np.linalg.norm(n);n=n/np.linalg.norm(n)
  else:
   VV=-Kp@C@W+Z@np.linalg.pinv(B)@(M-lam*np.eye(3))@W
   nn,nu=np.linalg.eigh(VV.T@VV)
   if nn[0]>1+1e-7:continue
   n=W@nu[:,0];v=VV@nu[:,0]
  if abs(n@v)>1e-6 or v@v>1+1e-6:raise RuntimeError(('ineligible',s,lam,n@v,v@v))
  u=-np.cross(n,v)
  cand.append((np.trace(A)-lam,u,'spectrum'))
 return max(cand,key=lambda x:x[0]),cand

def objective(T,c,u):
 bb=c+T.T@u;G=np.outer(bb,bb)+(1-u@u)*(T.T@T-np.outer(c,c))
 return np.linalg.eigvalsh(G)[-2:].sum()

if __name__=='__main__':
 rng=np.random.default_rng(20261103049);cases=[]
 # Arbitrary real data are allowed by the derivation, providing harsher tests than physical states.
 for i in range(100):
  T=rng.normal(size=(3,3));c=rng.normal(size=3);cases.append((T,c,'generic'))
 for i in range(100):
  tv=rng.uniform(.05,.95,3);tv[0]=np.linalg.norm((q:=rng.normal(size=3)))*.1;c=q*.1;T=np.diag(tv);cases.append((T,c,'rank2 K'))
 for i in range(100):
  s=rng.uniform(.05,.95);q=rng.normal(size=3);c=q/np.linalg.norm(q)*s;T=np.diag([s,s,rng.uniform(.05,.95)]);cases.append((T,c,'rank1 K'))
 for i in range(100):
  s=rng.uniform(.05,.95);q=rng.normal(size=3);c=q/np.linalg.norm(q)*s;T=s*np.eye(3);cases.append((T,c,'zero K'))
 # d parallel to a null vector of K; free v component W is present.
 for i in range(100):
  s=rng.uniform(.05,.95);c=np.array([0,0,s]);T=np.diag([rng.uniform(.05,.95),rng.uniform(.05,.95),s]);cases.append((T,c,'nonzero W'))
 # Repeated eigenvalues and c=0 with singular T.
 cases += [(np.diag(v),np.zeros(3),'zero c') for v in ([0,0,0],[.5,0,0],[.4,.4,0],[.8,.7,.7],[.6,.6,.6])]
 errors=[];max_witness_gap=0;max_sample_excess=0;types={}
 for i,(T,c,label) in enumerate(cases):
  (val,u,branch),cand=spec(T,c);actual=objective(T,c,u);gap=actual-val;max_witness_gap=max(max_witness_gap,abs(gap))
  if abs(gap)>2e-6:errors.append((i,label,'witness',val,actual,[(x[0],x[2]) for x in cand]))
  us=rng.normal(size=(500,3));us/=np.linalg.norm(us,axis=1)[:,None];us*=rng.uniform(0,1,size=(500,1))**(1/3)
  scores=[objective(T,c,z) for z in us];excess=max(scores)-val;max_sample_excess=max(max_sample_excess,excess)
  if excess>2e-6:errors.append((i,label,'sample',val,max(scores)))
  types[label]=types.get(label,0)+1
 print({'cases':len(cases),'types':types,'max_witness_gap':max_witness_gap,'max_sample_excess':max_sample_excess,'errors':errors[:20],'error_count':len(errors)})

if __name__=='__main__':
 import importlib.util, json, pathlib
 base=pathlib.Path(__file__).parent
 choices=[base/'unilateral_chsh.py',base/'chsh_unilateral_research'/'unilateral_chsh.py',base.parent/'unilateral_chsh.py']
 path=next(p for p in choices if p.exists())
 specmod=importlib.util.spec_from_file_location('root_solver',path);root_solver=importlib.util.module_from_spec(specmod);specmod.loader.exec_module(root_solver)
 root_errors=[];max_root_difference=0.;max_root_witness_gap=0.;empty_count=0
 for i,(T,c,label) in enumerate(cases):
  (val,_,_),_=spec(T,c)
  try:
   result=root_solver.canonical_optimum(T,c)
  except Exception as e:
   root_errors.append({'case':i,'label':label,'exception':str(e)});continue
  difference=abs(result['value']-val);max_root_difference=max(max_root_difference,difference)
  witness_gap=abs(objective(T,c,result['witness']['u'])-result['value']);max_root_witness_gap=max(max_root_witness_gap,witness_gap)
  if difference>2e-6 or witness_gap>2e-6:root_errors.append({'case':i,'label':label,'value_difference':difference,'witness_gap':witness_gap})
  if len(result['candidates'])==0:empty_count+=1
 summary={'seed':20261103049,'datasets':len(cases),'dataset_types':types,'random_filter_samples':len(cases)*500,'independent_max_witness_gap':float(max_witness_gap),'independent_max_sample_excess':float(max_sample_excess),'independent_errors':errors,'root_max_value_difference':float(max_root_difference),'root_max_witness_gap':float(max_root_witness_gap),'root_errors':root_errors,'root_empty_candidate_lists':empty_count,'scope':'Numerical checks of generic and exact-singular canonical data; does not constitute formal proof or exact arithmetic certification.'}
 out=pathlib.Path(__file__).with_name('independent_spectral_audit.json');out.write_text(json.dumps(summary,indent=2))
 print(json.dumps(summary,indent=2))

if __name__=='__main__':
 rngr=np.random.default_rng(482378);rotated_errors=[];max_rotated_difference=0.
 for i in range(100):
  ss=rngr.uniform(.05,.95);cc=np.array([0,0,ss]);TT=np.diag([rngr.uniform(.05,.95),rngr.uniform(.05,.95),ss]);O,_=np.linalg.qr(rngr.normal(size=(3,3)));Tr=O@TT
  (expected,_,_),_=spec(TT,cc)
  try:
   result=root_solver.canonical_optimum(Tr,cc);difference=abs(result['value']-expected);max_rotated_difference=max(max_rotated_difference,difference)
   if difference>2e-6:rotated_errors.append({'case':i,'expected':float(expected),'actual':float(result['value'])})
  except Exception as e:rotated_errors.append({'case':i,'exception':str(e)})
 rngp=np.random.default_rng(9845);physical_errors=[];max_physical_difference=0.
 TT=np.diag([.6,-.5,.2]);cc=np.array([0,0,.2]);rho=root_solver.state_from_bloch(np.zeros(3),cc,TT)
 for i in range(50):
  O,_=np.linalg.qr(rngp.normal(size=(3,3)));Tr=O@TT
  try:
   result=root_solver.canonical_optimum(Tr,cc);difference=abs(result['value']-.61);max_physical_difference=max(max_physical_difference,difference)
   if difference>2e-6:physical_errors.append({'case':i,'expected':.61,'actual':float(result['value'])})
  except Exception as e:physical_errors.append({'case':i,'exception':str(e)})
 summary.update({'rotated_common_kernel_cases':100,'rotated_common_kernel_max_difference':float(max_rotated_difference),'rotated_common_kernel_errors':rotated_errors,'physical_rotation_cases':50,'physical_rotation_state_eigenvalues':np.linalg.eigvalsh(rho).tolist(),'physical_rotation_exact_expected_squared_value':.61,'physical_rotation_max_difference':float(max_physical_difference),'physical_rotation_errors':physical_errors})
 out.write_text(json.dumps(summary,indent=2))
 print(json.dumps({k:v for k,v in summary.items() if k.startswith('rotated') or k.startswith('physical')},indent=2))
