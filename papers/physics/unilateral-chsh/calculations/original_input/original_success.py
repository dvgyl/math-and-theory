"""Original-input success-constrained unilateral CHSH.

The exact representation uses the Bob-side 3x3 Gram matrix and the
intersection of two balls. The numerical optimizer is a feasible multistart
reference, NOT a global certificate. Closed specialization formulas and
symbolic polynomial systems are supplied separately.
"""
from __future__ import annotations

import numpy as np
from scipy.optimize import minimize

PAULI = np.array([[[0, 1], [1, 0]], [[0, -1j], [1j, 0]],
                  [[1, 0], [0, -1]]], dtype=complex)
I2 = np.eye(2, dtype=complex)
I3 = np.eye(3)


def canonical_density(c, D):
    return (np.eye(4)+sum(c[j]*np.kron(I2, PAULI[j]) for j in range(3))
            +sum(D[i,j]*np.kron(PAULI[i], PAULI[j])
                 for i in range(3) for j in range(3)))/4


def sqrt_psd(A):
    values, vectors = np.linalg.eigh(A)
    return (vectors*np.sqrt(np.maximum(values, 0)))@vectors.conj().T


def original_density(c, D, a):
    """Undo positive whitening; canonical Alice marginal is I/2."""
    B = sqrt_psd(I2+np.einsum("i,ijk->jk", a, PAULI))
    BB = np.kron(B, I2)
    return BB@canonical_density(c, D)@BB.conj().T


def bob_gram(c, D, u):
    c, D, u = np.asarray(c), np.asarray(D), np.asarray(u)
    y = c+D.T@u
    G = (1-u@u)*(D.T@D-np.outer(c,c))+np.outer(y,y)
    return (G+G.T)/2


def score_squared(c, D, u):
    return float(np.linalg.eigvalsh(bob_gram(c,D,u))[1:].sum())


def score_gradient(c, D, u):
    """A gradient at a simple smallest eigenvalue; a selected subgradient otherwise."""
    G = bob_gram(c,D,u)
    _, V = np.linalg.eigh(G)
    P = I3-np.outer(V[:,0],V[:,0])
    Qc = D.T@D-np.outer(c,c)
    return 2*(D@P@(c+D.T@u)-u*np.trace(P@Qc))


def maximum_success(a, u):
    h = 1-np.dot(a,a)
    numerator = 1-np.dot(a,u)
    radicand = numerator*numerator-h*(1-np.dot(u,u))
    return float(h/(numerator+np.sqrt(max(0.0,radicand))))


def lens_slacks(a, u, p0):
    return np.array([1-u@u, (1-p0)**2-np.linalg.norm(a-p0*u)**2])


def radius_range(a_norm, p0):
    """Exact geometric formulas, evaluated in floating point."""
    if p0 == 0:
        return 0.0, 1.0
    return (max(0.0,1-(1-a_norm)/p0),
            min(1.0,(1+a_norm)/p0-1))


def minimum_norm_effect(a, p0):
    a = np.asarray(a, dtype=float)
    r = np.linalg.norm(a)
    rmin, _ = radius_range(r,p0)
    return np.zeros(3) if r == 0 else (rmin/r)*a


def concentration_filter(a, p0):
    """Largest-scale optimal filter for the conformal and correlated families.

    This is a filter on the ORIGINAL state, in its original Alice basis.
    It preserves the smaller-eigenvalue marginal component.
    """
    a = np.asarray(a, dtype=float)
    r = np.linalg.norm(a)
    if r == 0:
        return I2.copy()
    Pplus = (I2+np.einsum("i,ijk->jk",a/r,PAULI))/2
    Pminus = I2-Pplus
    factor = ((1-r)/(1+r) if p0 <= 1-r
              else (2*p0-1+r)/(1+r))
    return np.sqrt(max(0.0,factor))*Pplus+Pminus


def conformal_frontier(t, a_norm, p0):
    rmin, _ = radius_range(a_norm,p0)
    return t*t*(2-rmin*rmin)


def correlated_frontier(population, coherence_abs, p0):
    p = population
    if p == 0 or p == 1:
        return 1.0
    t2 = coherence_abs**2/(p*(1-p))
    rmin, _ = radius_range(abs(2*p-1),p0)
    return 1+t2*(1-rmin*rmin)


def product_frontier(a_norm, b_norm, p0):
    _, rmax = radius_range(a_norm,p0)
    return b_norm*b_norm*rmax*rmax


def purity_upper_bound(c, D, a, p0):
    alpha = np.sum(D*D)-np.dot(c,c)
    m = (alpha-1)/2
    rmin, rmax = radius_range(np.linalg.norm(a),p0)
    rbound = rmin if m>=0 else rmax
    return 1+m*(1-rbound*rbound)


def _positive_exit_root(A, B, C):
    if A == 0:
        return np.inf if B<=0 else -C/B
    disc=max(0.0,B*B-4*A*C)
    # C<=0 at the known interior point; the positive root is unambiguous.
    root=(-B+np.sqrt(disc))/(2*A)
    if B>0 and C<0:
        root=(-2*C)/(B+np.sqrt(disc))
    return max(0.0,root)


def _project_from_identity(a, u, p0):
    """Move along the segment from feasible u=a, preserving both balls."""
    if p0 == 1:
        return a.copy()
    d=u-a
    t1=_positive_exit_root(d@d,2*a@d,a@a-1)
    e=(1-p0)*a
    t2=_positive_exit_root(p0*p0*(d@d),-2*p0*(e@d),
                           e@e-(1-p0)**2)
    t=min(1.0,t1,t2)
    if t<1:
        t*=1-2e-12
    return a+t*d


def numerical_frontier(c, D, a, p0, starts=18, seed=240603945):
    """Feasible numerical candidate; multistart optimization is not a certificate."""
    c,D,a=map(lambda x:np.asarray(x,dtype=float),(c,D,a))
    if not (0<=p0<=1) or a@a>=1:
        raise ValueError("Require 0<=p0<=1 and a mixed original Alice marginal.")
    if c.shape!=(3,) or D.shape!=(3,3) or a.shape!=(3,):
        raise ValueError("Expected c,a length3 and D 3x3.")
    if np.linalg.eigvalsh(canonical_density(c,D))[0]<-1e-9:
        raise ValueError("The supplied canonical density matrix is not positive.")
    if p0==1:
        return {"status":"exact feasible effect at p0=1; numerical score",
                "score_squared":score_squared(c,D,a),"effect":a.tolist(),
                "maximum_success":1.0,"feasibility_slacks":[1-a@a,0.0]}
    rng=np.random.default_rng(seed)
    candidates=[a.copy(),minimum_norm_effect(a,p0)]
    for _ in range(max(0,starts-2)):
        u=rng.normal(size=3)
        u*=rng.uniform(0,1)/np.linalg.norm(u)
        candidates.append(_project_from_identity(a,u,p0))
    best=(score_squared(c,D,a),a.copy())
    successes=0
    constraints={"type":"ineq","fun":lambda u:lens_slacks(a,u,p0),
                 "jac":lambda u:np.array([-2*u,2*p0*(a-p0*u)])}
    for u0 in candidates:
        ans=minimize(lambda u:-score_squared(c,D,u),u0,
                     jac=lambda u:-score_gradient(c,D,u),
                     constraints=constraints,method="SLSQP",
                     options={"ftol":2e-12,"maxiter":400})
        successes+=int(ans.success)
        u=_project_from_identity(a,ans.x,p0)
        score=score_squared(c,D,u)
        if score>best[0]:
            best=(score,u)
    u=best[1]
    return {"status":"feasible numerical candidate; NOT a global certificate",
            "score_squared":best[0],"effect":u.tolist(),
            "maximum_success":maximum_success(a,u),
            "feasibility_slacks":lens_slacks(a,u,p0).tolist(),
            "optimization_starts":len(candidates),
            "successful_local_terminations":successes,
            "purity_upper_bound_float":purity_upper_bound(c,D,a,p0)}


def symbolic_problem(c, D, a, p0, threshold=1):
    """Exact SymPy polynomial activation system in u0,u1,u2."""
    import sympy as sp
    c,D,a=sp.Matrix(c),sp.Matrix(D),sp.Matrix(a)
    u=sp.Matrix(sp.symbols("u0:3",real=True))
    r2=(u.T*u)[0]
    y=c+D.T*u
    G=(1-r2)*(D.T*D-c*c.T)+y*y.T
    H=threshold*sp.eye(3)-sp.trace(G)*sp.eye(3)+G
    coefficients=[sp.trace(H),(sp.trace(H)**2-sp.trace(H*H))/2,H.det()]
    return {"variables":list(u),"unit_slack":1-r2,
            "success_slack":sp.expand((1-p0)**2-((a-p0*u).T*(a-p0*u))[0]),
            "gram":sp.simplify(G),"threshold_matrix":sp.simplify(H),
            "psd_coefficients":[sp.factor(v) for v in coefficients]}


def exact_psd_pseudoinverse(Q):
    """Rational rank-stratum formula for a concrete exact 3x3 PSD matrix."""
    import sympy as sp
    Q=sp.Matrix(Q)
    rank=Q.rank()
    e1=sp.trace(Q)
    if rank==0:
        return sp.zeros(3)
    if rank==1:
        return Q/e1**2
    e2=(e1**2-sp.trace(Q*Q))/2
    if rank==2:
        return ((e1**2-e2)*Q-e1*Q*Q)/e2**2
    return Q.adjugate()/Q.det()


def symbolic_ellipsoid_problem(Q, c, b, a_norm_squared, p0, threshold=1):
    """Exact rational problem on a fixed rank stratum, with at most 3 variables.

    Use exact SymPy rationals/algebraic inputs. Rank and eta signs are decided
    exactly; ambiguous symbolic sign assumptions are rejected rather than guessed.
    """
    import sympy as sp
    Q,c,b=sp.Matrix(Q),sp.Matrix(c),sp.Matrix(b)
    rank=Q.rank()
    Qplus=exact_psd_pseudoinverse(Q)
    g=b-c
    if sp.simplify(Q*Qplus*g-g)!=sp.zeros(3,1):
        raise ValueError("b-c must belong to the ellipsoid range.")
    eta=sp.simplify(a_norm_squared-(g.T*Qplus*g)[0])
    B=sp.Matrix.hstack(*Q.columnspace()) if rank else sp.zeros(3,0)
    xs=sp.symbols("w0:"+str(rank),real=True)
    w=B*sp.Matrix(xs) if rank else sp.zeros(3,1)
    q=(w.T*Qplus*w)[0]
    ell=((g-p0*w).T*Qplus*(g-p0*w))[0]
    variables=list(xs)
    extra=[]
    if rank<3:
        if eta==0:
            t=sp.Symbol("null_norm_squared",real=True)
            variables.append(t)
            extra.append(t)
            q+=t
            ell+=p0*p0*t
        elif eta.is_positive:
            k=sp.Symbol("null_overlap",real=True)
            variables.append(k)
            extra.append(k)
            q+=k*k/eta
            ell+=eta-2*p0*k+p0*p0*k*k/eta
        else:
            raise ValueError("eta must be exactly zero or provably positive.")
    elif eta!=0:
        raise ValueError("Full-rank shape must have eta=0.")
    G=(1-q)*(Q-c*c.T)+(c+w)*(c+w).T
    H=threshold*sp.eye(3)-sp.trace(G)*sp.eye(3)+G
    coeff=[sp.trace(H),(sp.trace(H)**2-sp.trace(H*H))/2,H.det()]
    return {"variables":variables,"rank":rank,"eta":eta,"range_basis":B,
            "conditional_shift":w,"effect_norm_squared":sp.factor(q),
            "feasibility_polynomials":[sp.factor(1-q),sp.factor((1-p0)**2-ell),*extra],
            "gram":sp.simplify(G),"threshold_matrix":sp.simplify(H),
            "psd_coefficients":[sp.factor(v) for v in coeff]}
