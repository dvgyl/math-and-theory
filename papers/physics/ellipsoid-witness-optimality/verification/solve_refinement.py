#!/usr/bin/env python3
"""Numerical implementation of the dossier's refinement SDP.

Floating-point output is a diagnostic, not an exact or Lean certificate.
Run `python verification/solve_refinement.py --output verification/sdp_examples.json`.
Use `new_results_verify.py` for exact rational primal/dual examples.
"""
from pathlib import Path
import argparse
import json
import numpy as np
import cvxpy as cp

I = np.eye(2, dtype=complex)
SIGMA = [np.array([[0,1],[1,0]],complex),
         np.array([[0,-1j],[1j,0]],complex),
         np.diag([1,-1]).astype(complex)]
PAULI = [I, *SIGMA]

def canonical_witness(c, A):
    c, A = np.asarray(c,float), np.asarray(A,float)
    return (np.eye(4,dtype=complex)
            + sum(c[i]*np.kron(SIGMA[i],I) for i in range(3))
            + sum(A[i,j]*np.kron(SIGMA[i],SIGMA[j])
                  for i in range(3) for j in range(3))) / 4

def L_of_matrix(E, c, A):
    """The complex-linear qubit map with affine Bloch action c+A r."""
    scalar = np.trace(E)/2
    coords = np.array([np.trace(P@E)/2 for P in SIGMA])
    return scalar*I + sum((scalar*c[i]+(A@coords)[i])*SIGMA[i]
                          for i in range(3))

def source_map(Q, c, A, symbolic=False, transpose_source=True):
    """M(Q)=(L tensor id)(Q^{Gamma_B}), in the basis 00,01,10,11."""
    out = 0
    for a in range(2):
        for d in range(2):
            E = np.zeros((2,2),complex); E[a,d]=1
            image = L_of_matrix(E,c,A)
            block = Q[2*a:2*a+2,2*d:2*d+2]
            if transpose_source:
                block=block.T
            out = out + (cp.kron(image,block) if symbolic else np.kron(image,block))
    return out

def solve_containment(W, c, A, solver='CLARABEL'):
    """The separate exact affine formulation, solved numerically here.

    Feasible iff E(W) is contained in the target, under ||b_W||<1,
    using the analytic positive-lift/decomposability theorem.
    """
    W=np.asarray(W,complex);c=np.asarray(c,float);A=np.asarray(A,float)
    P=cp.Variable((4,4),hermitian=True)
    Q=cp.Variable((4,4),hermitian=True)
    image=source_map(P,c,A,True,False)+source_map(Q,c,A,True)
    problem=cp.Problem(cp.Minimize(0),[P >> 0,Q >> 0,image==W])
    settings={'tol_gap_abs':1e-9,'tol_gap_rel':1e-9,'tol_feas':1e-9,
              'max_iter':300} if solver=='CLARABEL' else {'eps':1e-8,'max_iters':50000}
    problem.solve(solver=solver,**settings)
    result={'status':problem.status,'certificate_kind':'numerical only'}
    if P.value is not None and Q.value is not None:
        image_value=source_map(P.value,c,A,False,False)+source_map(Q.value,c,A)
        result.update({'equality_error':float(np.linalg.norm(image_value-W)),
                       'P_min_eigenvalue':float(np.linalg.eigvalsh(P.value).min()),
                       'Q_min_eigenvalue':float(np.linalg.eigvalsh(Q.value).min())})
    return result

def adjoint_map(X, c, A):
    # The orthogonal Pauli-product basis has squared Hilbert--Schmidt norm4.
    out=np.zeros((4,4),complex)
    for P in PAULI:
        for Q in PAULI:
            B=np.kron(P,Q)
            coefficient=np.trace(source_map(B,c,A).conj().T@X).real/4
            out += coefficient*B
    return (out+out.conj().T)/2

def bloch_data(W):
    a=np.array([np.trace(W@np.kron(P,I)).real for P in SIGMA])
    b=np.array([np.trace(W@np.kron(I,P)).real for P in SIGMA])
    T=np.array([[np.trace(W@np.kron(P,Q)).real for Q in SIGMA] for P in SIGMA])
    delta=1-float(b@b)
    if delta <= 0:
        raise ValueError('The Bob marginal is not positive definite.')
    K=T-np.outer(a,b)
    return {'a':a,'b':b,'T':T,'center':(a-T@b)/delta,
            'shape':K@(delta*np.eye(3)+np.outer(b,b))@K.T/delta**2,
            'chirality_determinant':float(np.linalg.det(K))}

def solve_refinement(W, c, A, solver='CLARABEL'):
    """Solve for a Hermitian source Q; do not project the numerical solution."""
    W=np.asarray(W,complex); c=np.asarray(c,float); A=np.asarray(A,float)
    if W.shape!=(4,4) or c.shape!=(3,) or A.shape!=(3,3):
        raise ValueError('Expected shapes W=(4,4), c=(3,), A=(3,3).')
    if not np.allclose(W,W.conj().T,atol=1e-12):
        raise ValueError('Input W must be Hermitian.')
    if abs(np.trace(W)-1)>1e-12:
        raise ValueError('Input W must have trace1.')
    Q=cp.Variable((4,4),hermitian=True)
    image=source_map(Q,c,A,symbolic=True)
    image=(image+image.H)/2
    residual=W-image
    constraints=[Q >> 0, residual >> 0]
    primal=cp.Problem(cp.Minimize(cp.real(cp.trace(Q))),constraints)
    settings={'tol_gap_abs':1e-9,'tol_gap_rel':1e-9,'tol_feas':1e-9,
              'max_iter':300} if solver=='CLARABEL' else {'eps':1e-8,'max_iters':50000}
    primal.solve(solver=solver,**settings)
    if primal.status not in ('optimal','optimal_inaccurate') or Q.value is None:
        return {'status':primal.status,'certificate_kind':'numerical only'}
    q=(Q.value+Q.value.conj().T)/2
    alpha=float(np.trace(q).real)
    m=source_map(q,c,A)
    residual_value=(W-m+(W-m).conj().T)/2
    # Solve the dual explicitly; avoid a solver-specific complex-cone scaling.
    X=cp.Variable((4,4),hermitian=True)
    adj=0
    for P in PAULI:
        for S in PAULI:
            B=np.kron(P,S)
            adj += cp.real(cp.trace(source_map(B,c,A).conj().T@X))/4*B
    dual=cp.Problem(cp.Maximize(-cp.real(cp.trace(X@W))),
                    [X >> 0, (np.eye(4)+adj+np.eye(4)+adj.H)/2 >> 0])
    dual.solve(solver=solver,**settings)
    result={'status':primal.status,'dual_status':dual.status,
            'certificate_kind':'numerical only; exact examples checked separately',
            'alpha':alpha,'Q_eigenvalues':np.linalg.eigvalsh(q).tolist(),
            'residual_eigenvalues':np.linalg.eigvalsh(residual_value).tolist(),
            'trace_residual':float(np.trace(residual_value).real),
            'Q_real':q.real.tolist(),'Q_imag':q.imag.tolist()}
    if alpha>0:
        data=bloch_data(m/alpha)
        result.update({'refined_center':data['center'].tolist(),
                       'refined_shape':data['shape'].tolist(),
                       'refined_chirality_determinant':data['chirality_determinant'],
                       'center_error':float(np.linalg.norm(data['center']-c)),
                       'shape_error':float(np.linalg.norm(data['shape']-A@A.T))})
    if X.value is not None:
        x=(X.value+X.value.conj().T)/2
        slack=np.eye(4)+adjoint_map(x,c,A)
        result.update({'dual_objective':float(-np.trace(x@W).real),
                       'duality_gap':float(alpha+np.trace(x@W).real),
                       'dual_X_eigenvalues':np.linalg.eigvalsh(x).tolist(),
                       'dual_slack_eigenvalues':np.linalg.eigvalsh(slack).tolist()})
    return result

def examples():
    z=np.zeros(3)
    yield 'class_d_equal_ellipsoid',canonical_witness(z,np.diag([1,1,-.5])),z,np.diag([1,1,.5]),1/3
    yield 'class_d_strict_interior',canonical_witness(z,np.diag([.75,.75,-.25])),z,np.diag([.75,.75,.25]),1/3
    yield 'class_c_spheres',canonical_witness(z,np.diag([.5,.5,.5])),z,np.diag([.75,.75,.75]),2/5
    A=np.diag([.75,0,.75]); W=.75*canonical_witness(z,A)+.25*np.eye(4)/4
    yield 'class_d_planar',W,z,A,1/4
    c=np.array([0,0,.2]); A=np.diag([.6,.6,.4])
    W=.9*canonical_witness(c,A)+.1*np.eye(4)/4
    yield 'class_c_translated',W,c,A,None
    yield 'refinement_feasible_but_containment_fails',canonical_witness(z,np.diag([1,1,-.8])),z,np.diag([1,1,.5]),2/15

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path)
    parser.add_argument('--solver',choices=['CLARABEL','SCS'],default='CLARABEL')
    args=parser.parse_args()
    report={'cvxpy_version':cp.__version__,'solver':args.solver,
            'warning':'These are numerical diagnostics, not exact proof certificates.',
            'examples':{}}
    for name,W,c,A,expected in examples():
        result=solve_refinement(W,c,A,args.solver)
        result['containment_program']=solve_containment(W,c,A,args.solver)
        if expected is not None:
            result['exact_expected_alpha']=expected
            result['alpha_error']=abs(result.get('alpha',float('inf'))-expected)
        report['examples'][name]=result
    data=json.dumps(report,indent=2)+'\n'
    if args.output:
        args.output.parent.mkdir(parents=True,exist_ok=True);args.output.write_text(data)
    print(json.dumps({k:{q:v[q] for q in ['status','alpha','duality_gap','alpha_error'] if q in v}
                      for k,v in report['examples'].items()},indent=2))

if __name__=='__main__':main()
