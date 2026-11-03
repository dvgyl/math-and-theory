"""Second-edition consequences of the unilateral CHSH theorem.

`exact_activation` uses SymPy rational/algebraic arithmetic and no eigenvalue
optimization. `exact_shortcut_value` returns exact algebraic cubic values for
rational input. The other routines use floating point and return diagnostics;
they must not be treated as exact certificates near a sign or rank boundary.
The success-probability frontier applies to the canonical input state.
"""
from __future__ import annotations

import numpy as np
from unilateral_chsh import cross_matrix


def elementary_signs(M):
    """Three elementary symmetric functions of a real symmetric matrix."""
    t = float(np.trace(M))
    return np.array([t, (t*t - np.trace(M @ M))/2, np.linalg.det(M)])


def ellipsoid_data(a, b, T):
    """Canonical (c,Q=D.T D), without taking any square root."""
    a, b, T = map(np.asarray, (a, b, T))
    h = float(1-a @ a)
    if h <= 0:
        raise ValueError("A full-rank filtered marginal is required.")
    X = T - np.outer(a, b)
    c = (b-T.T @ a)/h
    Q = X.T @ (np.eye(3)+np.outer(a, a)/h) @ X/h
    return c, (Q+Q.T)/2


def shortcut(D, c, tol=1e-10):
    """Exact theorem B_A^2=tr(A)-lambda_min(M), evaluated numerically.

    Valid for physical canonical states with alpha=tr(A)-|c|^2>1.
    The returned witness minimizes the boost radius in the winning
    eigenspace and therefore maximizes success among optimal filters.
    """
    D, c = np.asarray(D, float), np.asarray(c, float)
    A, s, d = D @ D.T, float(c @ c), D @ c
    alpha = float(np.trace(A)-s)
    if alpha <= 1+tol:
        raise ValueError("The strict purity guard is not numerically resolved.")
    K, C = A-s*np.eye(3), cross_matrix(d)
    if np.linalg.eigvalsh(K)[0] <= tol:
        raise ArithmeticError("K is not reliably positive definite.")
    V = -np.linalg.solve(K, C)
    M = A-C @ V
    M = (M+M.T)/2
    vals, vecs = np.linalg.eigh(M)
    keep = vals <= vals[0]+tol*max(1., np.linalg.norm(M, 2))
    N = vecs[:, keep]
    G = (V @ N).T @ (V @ N)
    gv, gz = np.linalg.eigh((G+G.T)/2)
    n = N @ gz[:, 0]
    v = V @ n
    u = -np.cross(n, v)
    value = float(np.trace(A)-vals[0])
    margin = float(vals[0]-s)
    return {
        "value": value, "B": float(np.sqrt(max(0., value))),
        "alpha": alpha, "purity_margin": (alpha-1)/2,
        "M": M, "eigenvalues": vals, "n": n, "v": v, "u": u,
        "canonical_success": 1/(1+np.linalg.norm(u)),
        "minimum_optimal_radius_squared": float(gv[0]),
        "maximum_optimal_radius_squared": float(gv[-1]),
        "strict_margin": margin,
        "eligibility_lower_bound": margin*float(n @ np.linalg.solve(K,n)),
        "orthogonality_residual": abs(float(n @ v)),
        "strict_eligibility_gap": float(1-v @ v),
        "spectrum_gap": float(vals[keep.sum()]-vals[0]) if keep.sum()<3 else None,
    }


def optimal_success_original(a, u):
    """Largest physical branch probability for a canonical effect u.

    The filter is kappa*sqrt(I+u.sigma)*(2*rho_A)^(-1/2), and its
    unscaled branch has trace one. Scaling to operator norm one gives this.
    """
    a, u = np.asarray(a,float), np.asarray(u,float)
    h, q = float(1-a @ a), float(1-a @ u)
    if h <= 0 or np.linalg.norm(u)>1+1e-10:
        raise ValueError("Require full-rank marginal and an effect in the ball.")
    disc = q*q-h*float(1-u @ u)
    if disc < -1e-12:
        raise ArithmeticError("Negative discriminant beyond numerical tolerance.")
    return h/(q+np.sqrt(max(0.,disc)))


def success_frontier(D, c, probability, tol=1e-10):
    """Best B^2 with canonical physical success >= probability.

    Preconditions: 1/2 <= probability <= 1 and K+iC positive definite.
    Uses the exact one-dimensional convex dual; minimizes it numerically.
    For probability=1 the only effect is zero, so no filtering occurs.
    """
    if not .5 <= probability <= 1:
        raise ValueError("Canonical success threshold must be in [1/2,1].")
    D, c = np.asarray(D,float), np.asarray(c,float)
    A, s = D @ D.T, float(c @ c)
    K, C = A-s*np.eye(3), cross_matrix(D @ c)
    if np.linalg.eigvalsh(K.astype(complex)+1j*C)[0] <= tol:
        raise ValueError("This frontier theorem requires K+iC positive definite.")
    radius = 1/probability-1
    if radius == 0:
        values, vectors = np.linalg.eigh(A)
        return {"value":float(values[1]+values[2]), "tau":float("inf"),
                "u":np.zeros(3), "n":vectors[:,0], "radius":0., "plateau":False}

    def data(tau):
        V = -np.linalg.solve(K+tau*np.eye(3),C)
        M = A-C @ V
        vals, N = np.linalg.eigh((M+M.T)/2)
        keep = vals <= vals[0]+tol*max(1.,np.linalg.norm(M,2))
        N = N[:,keep]
        G = (V @ N).T @ (V @ N)
        r2, Z = np.linalg.eigh((G+G.T)/2)
        return float(np.trace(A)+tau*radius**2-vals[0]), V, N, r2, Z

    start = data(0.)
    constraint_tol = tol*max(radius**2,1e-12)
    if start[3][0] <= radius**2+constraint_tol:
        tau, result, plateau = 0., start, True
    else:
        high = 1.
        while data(high)[3][-1] > radius**2:
            high *= 2
        low = 0.
        # Bisection of the monotone subgradient also handles an eigenvalue
        # crossing, where a scalar smooth optimizer need not reconstruct a
        # feasible witness from an arbitrarily selected eigenvector.
        for _ in range(100):
            tau = (low+high)/2
            result = data(tau)
            if result[3][0]-constraint_tol <= radius**2 <= result[3][-1]+constraint_tol:
                break
            if result[3][0] > radius**2:
                low = tau
            else:
                high = tau
        plateau = False
    value, V, N, r2, Z = result
    if plateau or len(r2)==1 or r2[-1]-r2[0] <= tol:
        n = N @ Z[:,0]
    else:
        # At a degenerate dual minimum the entire lowest eigenspace is
        # active. This real combination realizes the required radius.
        weight = np.clip((radius**2-r2[0])/(r2[-1]-r2[0]),0.,1.)
        n = N @ (np.sqrt(1-weight)*Z[:,0]+np.sqrt(weight)*Z[:,-1])
    v = V @ n
    u = -np.cross(n,v)
    root = np.sqrt(max(0.,1-u @ u))
    Du = (root*np.eye(3)+np.outer(u,u)/(1+root))@D+np.outer(u,c)
    singular = np.linalg.svd(Du,compute_uv=False)
    witness_value = float(singular[0]**2+singular[1]**2)
    return {"value":value,"tau":tau,"u":u,"n":n,"v":v,"radius":radius,
            "realized_radius":float(np.linalg.norm(u)),"plateau":plateau,
            "dual_constraint_residual":float(v @ v-radius**2),
            "actual_success":1/(1+np.linalg.norm(u)),
            "witness_value":witness_value,"duality_gap":value-witness_value}


def exact_activation(a, b, T, side="A"):
    """Quantifier-free exact activation criterion for rational/algebraic data.

    Input is the Bloch data of a PHYSICAL trace-one two-qubit state. This
    routine does not verify input positivity. No Float inputs are accepted.
    Returned signs are exact and determine both filtered violation and
    activation from an initially CHSH-nonviolating state.
    """
    import sympy as sp
    a,b,T = sp.Matrix(a),sp.Matrix(b),sp.Matrix(T)
    if any(x.has(sp.Float) for x in list(a)+list(b)+list(T)):
        raise TypeError("Use exact rational or algebraic SymPy inputs, not floats.")
    if side.upper()=="B":
        a,b,T = b,a,T.T
    elif side.upper()!="A":
        raise ValueError("side must be A or B")
    simp = sp.simplify
    aa,bb = simp((a.T*a)[0]),simp((b.T*b)[0])
    h = simp(1-aa)
    raw_guard = simp(sp.trace(T*T.T)+aa-bb-1)
    A0 = T*T.T
    initial_test = A0-(sp.trace(A0)-1)*sp.eye(3)

    def signs_of(M):
        tr = sp.trace(M)
        return tuple(map(simp,(tr,(tr*tr-sp.trace(M*M))/2,M.det())))

    def exact_sign(x):
        sign=sp.sign(x)
        if sign not in (-1,0,1):
            raise ArithmeticError(f"SymPy could not decide an exact real sign: {x}")
        return int(sign)

    init_coeff = signs_of(initial_test)
    initial_nonviolating = all(exact_sign(x)>=0 for x in init_coeff)
    out = {"raw_purity_guard":raw_guard,"initial_coefficients":init_coeff,
           "initial_nonviolating":initial_nonviolating}
    if exact_sign(h)==0:
        out.update(filtered_violation=False,hidden_activation=False,
                   reason="pure filtered marginal: product state")
        return out
    if exact_sign(h)<0:
        raise ValueError("Unphysical marginal Bloch vector")
    if exact_sign(raw_guard)<=0:
        out.update(filtered_violation=False,hidden_activation=False,
                   reason="necessary purity guard fails")
        return out
    X=T-a*b.T
    c=(b-T.T*a)/h
    Q=X.T*(sp.eye(3)+a*a.T/h)*X/h
    Q=Q.applyfunc(simp)
    s=simp((c.T*c)[0])
    K=Q-s*sp.eye(3)
    delta,q,t=map(simp,(K.det(),(c.T*Q*K*c)[0],sp.trace(Q)-1))
    z=K*c
    R=(Q.det()*(delta-q)*sp.eye(3)+(s*q-t*delta)*Q.adjugate()
       +Q.det()*z*z.T).applyfunc(simp)
    coeff=signs_of(R)
    signs=tuple(exact_sign(x) for x in coeff)
    violation=any(x<0 for x in signs)
    out.update(c=c,Q=Q,alpha=simp(sp.trace(Q)-s),ellipsoid_test_matrix=R,
               activation_coefficients=coeff,activation_signs=signs,
               filtered_violation=violation,
               hidden_activation=bool(initial_nonviolating and violation),
               reason="strict purity guard plus exact ellipsoid polynomial signs")
    return out


def sensitivity(D,c,n,v):
    """Gradient of B_A^2 on a simple, strictly feasible winning branch."""
    D,c,n,v = map(lambda x:np.asarray(x,float),(D,c,n,v))
    u=-np.cross(n,v)
    return (2*((np.eye(3)-np.outer(n,n)-np.outer(v,v))@D+np.outer(u,c)),
            2*(D.T@u+(v@v)*c))


def exact_shortcut_value(a,b,T,side="A"):
    """An exact cubic algebraic value, using rational original Bloch data.

    Requires the strict purity guard. SymPy's real-root objects provide exact
    values without choosing numerical roots or writing unstable Cardano
    radicals. Physicality of the input state is a mathematical precondition.
    """
    import sympy as sp
    cert=exact_activation(a,b,T,side)
    if 'Q' not in cert:
        raise ValueError("The strict purity guard is required for this shortcut.")
    Q,c=cert['Q'],cert['c']
    s=sp.simplify((c.T*c)[0]); K=Q-s*sp.eye(3)
    delta=sp.simplify(K.det()); q=sp.simplify((c.T*Q*K*c)[0])
    z=K*c; J=(delta-q)*K
    nu=sp.Symbol('nu',real=True)
    U=nu*sp.eye(3)-J
    polynomial=sp.Poly(sp.expand(U.det()-(z.T*Q*U.adjugate()*z)[0]),nu)
    roots=sp.polys.polytools.real_roots(polynomial)
    if len(roots)!=3:
        raise ArithmeticError("A physical guarded input must give three positive real roots.")
    value=sp.simplify(cert['alpha']-roots[0]/delta)
    return {'squared_value':value,'scaled_eigenvalue_polynomial':polynomial,
            'scaled_eigenvalues':roots,'delta':delta,'alpha':cert['alpha']}


def rank_two_value_from_bloch(a,b,T,side="A"):
    """Closed value for a state KNOWN to have density-matrix rank <=2.

    This routine does not infer rank numerically. Mixed marginal is required;
    for an exactly pure filtered marginal the product-state rule applies.
    """
    a,b,T=map(lambda x:np.asarray(x,float),(a,b,T))
    if side.upper()=='B': a,b,T=b,a,T.T
    elif side.upper()!='A': raise ValueError('side must be A or B')
    h=float(1-a@a)
    if h<=1e-12:
        raise ArithmeticError('Resolve the marginal rank exactly or use higher precision.')
    guard=float(np.sum(T*T)+a@a-b@b-1)
    return 1+max(0.,guard)/(2*h)


def axial_success_frontier(t,r,c0,probability):
    """Closed piecewise frontier for D=diag(t,-t,r), c=(0,0,c0).

    Domain: 0<=r<=1, 0<=c0<=1-r, 4t^2<=(1+r)^2-c0^2,
    and K+iC positive definite. Returns the exact-formula value evaluated
    in floating point, together with a maximizing effect direction.
    """
    x,s,g=float(t*t),float(c0*c0),float(r*c0)
    k,kz=x-s,r*r-s
    if not (.5<=probability<=1 and 0<=r<=1 and 0<=c0<=1-r+1e-13
            and 4*x<=(1+r)**2-s+1e-13):
        raise ValueError('Parameters are outside the stated physical family.')
    if min(k-g,kz)<=0:
        raise ValueError('The closed frontier theorem requires K+iC positive definite.')
    R=1/probability-1
    if g==0:
        return {'value':max(2*x,x+r*r),'u':np.zeros(3),'mode':'identity'}
    Rstar=g/k
    if x>r*r:
        tau_c=g*g/(x-r*r)-k
        if tau_c<=0:
            return {'value':2*x,'u':np.zeros(3),'mode':'identity'}
        Rc=(x-r*r)/g
        if R<Rc:
            theta=(R/Rc)**2
            u=np.array([-R*np.sqrt(max(0.,1-theta)),0.,R*R/Rc])
            return {'value':2*x+tau_c*R*R,'u':u,'mode':'tilted',
                    'transition_radius':Rc,'plateau_radius':Rstar}
    radius=min(R,Rstar)
    return {'value':x+r*r+2*g*radius-k*radius**2,
            'u':np.array([0.,0.,radius]),
            'mode':'plateau' if R>=Rstar else 'axial','plateau_radius':Rstar}


def value_error_bound(A_error,s_error,d_error):
    """Universal error bound from canonical-data operator/Euclidean errors."""
    if min(A_error,s_error,d_error)<0:
        raise ValueError("Error bounds must be nonnegative")
    return 2*A_error+s_error+2*d_error

