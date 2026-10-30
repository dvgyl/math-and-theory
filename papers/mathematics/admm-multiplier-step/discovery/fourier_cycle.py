"""Fourier/SOCP reduction of cyclic convex-interpolation ADMM cycles.

Exploratory floating-point solver only. No feasibility output is a proof.
Conventions: x_i=z_i+v_i-v_(i-1), u_i=tau*v_i.
Each positive frequency has a2x2 Hermitian PSD Gram matrix for (z,v).
"""
import argparse
import json
from pathlib import Path
import time
import numpy as np
import cvxpy as cp


class FourierCycle:
    def __init__(self, period, weighted_slack=True, residual_normalization=False):
        self.K = K = int(period)
        self.freqs = np.arange(1, K//2+1)
        self.theta = 2*np.pi*self.freqs/K
        self.H = cp.Variable((len(self.freqs),4))
        self.tau = cp.Parameter()
        self.slack = cp.Variable()
        a,b,x,y = [self.H[:,i] for i in range(4)]
        constraints = [cp.sum(cp.multiply(abs(1-np.exp(-1j*self.theta))**2,b))==1]
        if not residual_normalization:
            constraints = [cp.sum(a+b)==1]
        for j in range(len(self.freqs)):
            constraints += [cp.SOC(a[j]+b[j],cp.hstack([a[j]-b[j],2*x[j],2*y[j]]))]
        if K%2==0:
            constraints.append(y[-1]==0)
        self.M0, self.M1 = self.coefficients(0), self.coefficients(1)-self.coefficients(0)
        offsets = np.arange(1,K)
        scale = 1-np.cos(2*np.pi*offsets/K) if weighted_slack else np.ones(K-1)
        self.scales = np.r_[scale,scale]
        self.margins = (self.M0+self.tau*self.M1) @ cp.reshape(self.H,(4*len(self.freqs),),order='C')
        self.normal_constraints = self.margins >= self.slack*self.scales
        constraints.append(self.normal_constraints)
        self.problem = cp.Problem(cp.Maximize(self.slack),constraints)

    def coefficients(self,tau):
        r=np.exp(-1j*self.theta)
        delta=1-r
        c=1+(tau-1)*r
        cbar=np.conjugate(c)
        LC=np.stack([-np.conjugate(delta),-cbar*delta,
                     -abs(delta)**2-cbar,1j*(cbar-abs(delta)**2)],axis=1)
        LD=np.stack([np.zeros_like(c),np.zeros_like(c),cbar,-1j*cbar],axis=1)
        rows=[]
        for L in [LC,LD]:
            for k in range(1,self.K):
                rows.append(-np.real((np.exp(1j*k*self.theta)-1)[:,None]*L).ravel())
        return np.array(rows)

    def solve(self,tau,save=None):
        started=time.monotonic()
        self.tau.value=float(tau)
        value=self.problem.solve(solver='CLARABEL',tol_gap_abs=1e-10,
            tol_gap_rel=1e-10,tol_feas=1e-10,max_iter=300)
        H=np.array(self.H.value)
        masses=H[:,0]+H[:,1]
        result=dict(K=self.K,tau=float(tau),slack=float(value),status=self.problem.status,
            mass_by_frequency=masses.tolist(),blocks=H.tolist(),
            dual_normals=np.array(self.normal_constraints.dual_value).tolist(),
            seconds=time.monotonic()-started)
        result['minimum_cone_eigenvalue']=float(min(
            np.linalg.eigvalsh([[a,x+1j*y],[x-1j*y,b]])[0] for a,b,x,y in H))
        result['minimum_actual_margin']=float(min(self.coefficients(tau)@H.ravel()))
        if save:
            Path(save).write_text(json.dumps(result,indent=2))
        return result

    def real_coordinates(self):
        """Factor the Hermitian blocks into real cyclic z,v coordinates."""
        zz=[];vv=[]
        for theta,(a,b,x,y) in zip(self.theta,self.H.value):
            H=np.array([[a,x+1j*y],[x-1j*y,b]])
            ev,Q=np.linalg.eigh(H)
            F=np.sqrt(np.maximum(ev,0))[:,None]*Q.conj().T
            z=F[:,0];v=F[:,1]
            phases=np.exp(1j*np.arange(self.K)*theta)[:,None]
            zz += [(phases*z).real,(phases*z).imag]
            vv += [(phases*v).real,(phases*v).imag]
        return np.concatenate(zz,axis=1),np.concatenate(vv,axis=1)

    def direct_check(self,tau):
        z,v=self.real_coordinates()
        x=z+v-np.roll(v,1,axis=0)
        a=np.roll(z,1,axis=0)-tau*np.roll(v,1,axis=0)-x
        b=x+tau*np.roll(v,1,axis=0)-z
        direct=[]
        for points,normals in [(x,a),(z,b)]:
            direct += [float(normals[0]@(points[0]-points[k])) for k in range(1,self.K)]
        fourier=self.coefficients(tau)@self.H.value.ravel()
        return dict(maximum_fourier_direct_error=float(np.max(np.abs(fourier-direct))),
                    minimum_direct_margin=min(direct),
                    residual_squared=float(np.sum((x[0]-z[0])**2)))


def main():
    p=argparse.ArgumentParser()
    p.add_argument('--K',type=int,nargs='+',default=[5,8,16,32,64])
    p.add_argument('--tau',type=float,nargs='+',default=[1.65,1.8,1.9,1.99])
    p.add_argument('--output',default='fourier_results.json')
    p.add_argument('--residual-normalization',action='store_true')
    p.add_argument('--unweighted-slack',action='store_true')
    args=p.parse_args()
    rows=[]
    for K in args.K:
        model=FourierCycle(K,weighted_slack=not args.unweighted_slack,
            residual_normalization=args.residual_normalization)
        for tau in args.tau:
            result=model.solve(tau)
            result.update(model.direct_check(tau))
            rows.append(result)
            print(json.dumps({k:v for k,v in result.items() if k not in
                ['blocks','mass_by_frequency','dual_normals']}),flush=True)
            Path(args.output).write_text(json.dumps(rows,indent=2))


if __name__=='__main__': main()
