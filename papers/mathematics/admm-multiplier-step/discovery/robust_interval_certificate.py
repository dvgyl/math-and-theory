"""Search an interval certificate in scaled coordinates v=u/tau.

All interpolation matrices are affine in tau. The same nonnegative
multipliers and affine-in-tau potential matrices, certified at two endpoints,
therefore certify the whole interval. Function-value potential terms are zero.
Residual decrease is represented exactly through consecutive differences,
removing its unavoidable constant-sequence nullspace.
"""
import argparse,json,time
from pathlib import Path
import numpy as np
import cvxpy as cp


def symouter(a,b):return (np.outer(a,b)+np.outer(b,a))/2


def matrices(tau,m):
    dim=2*(m+1);E=np.eye(dim);Z=E[::2];V=E[1::2];zero=np.zeros(dim)
    X=[zero]+[Z[j]+V[j]-V[j-1] for j in range(1,m+1)]
    AA=[zero]+[Z[j-1]-tau*V[j-1]-X[j] for j in range(1,m+1)]
    BB=[zero]+[X[j]+tau*V[j-1]-Z[j] for j in range(1,m+1)]
    fv=np.eye(2*m);fvzero=np.zeros(2*m);data=[]
    for name,points,grads,values in [
        ('f',X,AA,[fvzero]+list(fv[:m])),
        ('g',[zero]+list(Z[1:]),BB,[fvzero]+list(fv[m:]))]:
        for i in range(m+1):
            for j in range(m+1):
                if i!=j:data.append(dict(name=name,i=i,j=j,
                    Q=-symouter(grads[i],points[j]-points[i]),F=values[j]-values[i]))
    S0=E[:2*m];S1=E[2:]
    D=E[2:]-E[:-2]
    diss=symouter(Z[m]-Z[m-1],Z[m]-Z[m-1])+symouter(V[m]-V[m-1],V[m]-V[m-1])
    coerc=symouter(Z[m-1],Z[m-1])+symouter(V[m-1],V[m-1])
    return data,S0,S1,D,diss,coerc


def solve(lo,hi,m,positive_floor=0,pure_lower=False,certificate_scale=1):
    data0,*_=matrices(lo,m)
    lower_indices=[i for i,r in enumerate(data0) if r['i']<m and r['j']<m]
    lam=cp.Variable(len(data0));mu=cp.Variable(len(lower_indices))
    constraints=[lam>=positive_floor/certificate_scale,mu>=positive_floor/certificate_scale,
        np.array([r['F'] for r in data0]).T@lam==0,
        np.array([data0[i]['F'] for i in lower_indices]).T@mu==0]
    if pure_lower:constraints.append(mu==0)
    Ps=[];Ss=[];Ls=[]
    for tau in [lo,hi]:
        data,S0,S1,D,diss,coerc=matrices(tau,m)
        P=cp.Variable((2*m,2*m),symmetric=True)
        T=cp.Variable((2*m,2*m),symmetric=True)
        qsum=cp.reshape(np.column_stack([r['Q'].ravel() for r in data])@lam,diss.shape,order='C')
        lqsum=cp.reshape(np.column_stack([data[i]['Q'].ravel() for i in lower_indices])@mu,diss.shape,order='C')
        M=S0.T@P@S0-S1.T@P@S1-diss/certificate_scale-qsum
        L=(S0.T@P@S0-coerc/certificate_scale-lqsum)[:2*m,:2*m]
        equality=M-D.T@T@D
        constraints += [equality[np.triu_indices(len(D[0]))]==0,
            T>>np.eye(2*m)/certificate_scale,L>>np.eye(2*m)/certificate_scale]
        Ps.append(P);Ss.append(T);Ls.append(L)
    objective=sum(cp.norm(P,'fro') for P in Ps)+cp.sum(lam)+cp.sum(mu)
    prob=cp.Problem(cp.Minimize(objective),constraints);started=time.monotonic()
    value=prob.solve(solver='CLARABEL',tol_gap_abs=1e-11,tol_gap_rel=1e-11,
        tol_feas=1e-11,max_iter=400)
    out=dict(interval=[lo,hi],memory=m,status=prob.status,objective=float(value),
        seconds=time.monotonic()-started,positive_multiplier_floor=positive_floor,pure_lower=pure_lower,
        certificate_scale=certificate_scale)
    if lam.value is not None:
        out.update(multipliers=(certificate_scale*lam.value).tolist(),
            lower_multipliers=(certificate_scale*mu.value).tolist(),
            P=[(certificate_scale*P.value).tolist() for P in Ps],
            T=[(certificate_scale*T.value).tolist() for T in Ss],
            lower_matrices=[(certificate_scale*L.value).tolist() for L in Ls],
            min_eigenvalues_T=[float(certificate_scale*np.linalg.eigvalsh(T.value)[0]) for T in Ss],
            min_eigenvalues_lower=[float(certificate_scale*np.linalg.eigvalsh(L.value)[0]) for L in Ls],
            interpolation_indices=[{k:r[k] for k in ['name','i','j']} for r in data0],
            lower_indices=lower_indices)
    return out


def main():
    p=argparse.ArgumentParser();p.add_argument('--lo',type=float,default=1.6)
    p.add_argument('--hi',type=float,default=1.8);p.add_argument('--memory',type=int,default=6)
    p.add_argument('--floor',type=float,default=0)
    p.add_argument('--pure-lower',action='store_true')
    p.add_argument('--scale',type=float,default=1)
    p.add_argument('--output',default='robust_interval_result.json')
    args=p.parse_args()
    try:out=solve(args.lo,args.hi,args.memory,args.floor,args.pure_lower,args.scale)
    except Exception as e:out=dict(interval=[args.lo,args.hi],memory=args.memory,error=type(e).__name__+': '+str(e))
    Path(args.output).write_text(json.dumps(out,indent=2))
    print(json.dumps({k:v for k,v in out.items() if k in ['interval','memory','status','objective','seconds',
        'min_eigenvalues_T','min_eigenvalues_lower','error']}),flush=True)


if __name__=='__main__':main()
