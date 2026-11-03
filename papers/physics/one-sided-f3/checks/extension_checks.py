#!/usr/bin/env python3
"""Probability-constrained one-sided F3: finite algebraic candidate evaluator.

This implements the two-ball lens theorem in extensions_independent.txt.
The mathematical prescription is exact.  This evaluator is floating-point,
and its comparison with SLSQP is a falsification check, not a proof.

Dependencies: numpy, scipy.  The nonglobal-sphere example is also checked
separately with exact fractions by exact_nonglobal_example().
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as F
from pathlib import Path
import json
import numpy as np
from numpy.linalg import eigh, eigvalsh, eigvals, norm
from scipy.optimize import minimize

EPS = 2e-9
SIGMA = np.array([[[0, 1], [1, 0]], [[0, -1j], [1j, 0]],
                  [[1, 0], [0, -1]]], dtype=complex)
I2 = np.eye(2, dtype=complex)


def quadratic(tau, H, g, x):
    return float(tau + 2 * g @ x + x @ H @ x)


def filter_probability_capacity(a, x):
    """Largest physical success probability for a fixed canonical direction."""
    delta = 1 - a @ a
    s = 1 - a @ x
    discriminant = s * s - delta * (1 - x @ x)
    assert discriminant > -2e-12
    return float(delta / (s + np.sqrt(max(0., discriminant))))


def best_success_optimal_family(a, x0, kernel, sphere_only=False):
    """Exact radical prescription for the best rate on an optimal family.

    kernel has orthonormal columns, x0 is orthogonal to those columns,
    and the family is x0+z with z in kernel and |z|<=sqrt(1-|x0|^2).
    If sphere_only, equality is imposed on |z|.  In that case a nonempty
    sphere family is an input hypothesis.
    """
    r = float(np.sqrt(max(0., 1 - x0 @ x0)))
    aK = kernel @ (kernel.T @ a)
    aR = a - aK
    alpha = norm(aK)
    u = a @ x0
    delta = 1 - a @ a
    pb = float(delta / (2 * (1 - u - r * alpha)))
    if sphere_only or r < 2e-12 or pb * r <= alpha + 2e-13:
        if alpha > 2e-12:
            x = x0 + r * aK / alpha
        elif r > 2e-12:
            assert kernel.shape[1] > 0
            x = x0 + r * kernel[:, 0]
        else:
            x = x0.copy()
        return {'p': pb, 'x': x, 'branch': 'boundary'}
    constant = 1 - aR @ aR
    discriminant = (1 - u)**2 - r**2 * constant
    assert discriminant > -2e-12
    pi = float(constant / (1 - u + np.sqrt(max(0., discriminant))))
    x = x0 + aK / pi
    return {'p': pi, 'x': x, 'branch': 'interior'}


def best_success_checks():
    """Independent convex SOC-reference checks of the radical rate formula."""
    rng = np.random.default_rng(2026110303)
    max_gap = 0.; max_capacity_error = 0.; max_feasibility_error = 0.
    max_effect_capacity_error = 0.; max_reference_feasibility_error = 0.
    disk_cases = 0; sphere_cases = 0; successful_references = 0
    branches = {'boundary': 0, 'interior': 0}
    for kdim in range(4):
        for index in range(24):
            Q, _ = np.linalg.qr(rng.normal(size=(3, 3)))
            K = Q[:, :kdim]
            a = rng.normal(size=3); a *= rng.uniform(0., .98) / norm(a)
            x0 = np.zeros(3)
            if kdim < 3:
                coordinates = rng.normal(size=3-kdim)
                coordinates *= rng.uniform(0., .99) / norm(coordinates)
                x0 = Q[:, kdim:] @ coordinates
            ans = best_success_optimal_family(a, x0, K)
            branches[ans['branch']] += 1
            r = np.sqrt(max(0., 1-x0@x0))
            # Convex formulation in (p,y), with y=p*z in ker(A):
            # |y|<=p*r and |a-p*x0-K*y|<=1-p.
            def sphere_cap(v):
                return v[0]*r - norm(v[1:])
            def effect_cap(v):
                return 1-v[0]-norm(a-v[0]*x0-K@v[1:])
            pstart = min(.05, filter_probability_capacity(a, x0)*.5)
            start = np.r_[pstart, np.zeros(kdim)]
            reference = minimize(lambda v: -v[0], start, method='SLSQP',
                bounds=[(1e-10, 1.)]+[(None, None)]*kdim,
                constraints=[{'type':'ineq','fun':sphere_cap},
                             {'type':'ineq','fun':effect_cap}],
                options={'ftol':2e-12, 'maxiter':1500})
            gap = abs(ans['p']-reference.x[0])
            max_reference_feasibility_error=max(max_reference_feasibility_error,
                max(0.,-sphere_cap(reference.x),-effect_cap(reference.x)))
            if reference.success:
                successful_references += 1
            assert gap < 3e-6, (kdim, ans, reference)
            max_gap = max(max_gap, gap)
            max_capacity_error=max(max_capacity_error,
                abs(filter_probability_capacity(a,ans['x'])-ans['p']))
            W=positive_power(I2+np.einsum('i,ijk->jk',a,SIGMA),-.5)
            E=I2+np.einsum('i,ijk->jk',ans['x'],SIGMA)
            operator_capacity=1/max(eigvalsh(W@E@W))
            max_effect_capacity_error=max(max_effect_capacity_error,
                abs(operator_capacity-ans['p']))
            assert abs(operator_capacity-ans['p'])<2e-11
            max_feasibility_error=max(max_feasibility_error,
                max(0., norm(ans['x'])-1,
                    norm(a-ans['p']*ans['x'])-(1-ans['p']),
                    norm((np.eye(3)-K@K.T)@(ans['x']-x0))))
            disk_cases += 1
            if kdim:
                boundary = best_success_optimal_family(a, x0, K, True)
                assert abs(norm(boundary['x'])-1)<2e-12
                assert abs(filter_probability_capacity(a,boundary['x'])-boundary['p'])<2e-11
                directions=rng.normal(size=(80,kdim))
                directions/=np.linalg.norm(directions,axis=1)[:,None]
                for direction in directions:
                    test_x=x0+r*K@direction
                    assert filter_probability_capacity(a,test_x)<=boundary['p']+2e-11
                sphere_cases += 1
    # Structured endpoints: a flat objective permits identity; unique
    # interior optimizer; unique rank-one optimizer; exact branch equality.
    structured=[]
    for a,x0,K,sphere in [
        (np.array([.2,.3,.4]),np.zeros(3),np.eye(3),False),
        (np.array([.2,.3,.4]),np.array([.1,-.2,.3]),np.zeros((3,0)),False),
        (np.array([.2,.3,.4]),np.array([1.,0.,0.]),np.zeros((3,0)),True),
        (np.array([.5,0.,0.]),np.array([0.,.6,0.]),np.eye(3)[:,:1],False),
    ]:
        ans=best_success_optimal_family(a,x0,K,sphere)
        assert abs(filter_probability_capacity(a,ans['x'])-ans['p'])<2e-11
        structured.append({'p':ans['p'],'branch':ans['branch'],'x':ans['x'].tolist()})
    assert abs(structured[0]['p']-1)<2e-12
    assert abs(structured[3]['p']-F(5,8))<2e-12
    assert norm(np.array(structured[3]['x'])-np.array([.8,.6,0.]))<2e-12
    return {'seed':2026110303,'affine_disk_cases':disk_cases,
        'boundary_sphere_cases':sphere_cases,'random_directions_per_sphere':80,
        'kernel_dimensions':[0,1,2,3],'radical_branches':branches,
        'successful_convex_references':successful_references,
        'max_probability_gap_against_convex_reference':max_gap,
        'max_scalar_radical_capacity_error':max_capacity_error,
        'max_direct_2x2_operator_capacity_error':max_effect_capacity_error,
        'max_reference_feasibility_residual':max_reference_feasibility_error,
        'max_feasibility_residual':max_feasibility_error,
        'structured_endpoints':structured,'all_passed':True}


def pure_state_frontier_checks():
    """Direct complex filtering checks of the exact Schmidt frontier."""
    max_formula_error=0.;max_lens_error=0.;max_probability_error=0.;cases=0
    for epsilon in [0.,1e-4,.01,.1,.25,.5]:
        psi=np.array([np.sqrt(1-epsilon),0.,0.,np.sqrt(epsilon)],complex)
        rho=np.outer(psi,psi.conj())
        probabilities=([.01,.2,.5,1.] if epsilon==0 else
            sorted(set([epsilon*.5,epsilon,min(1.,2*epsilon),
                        min(1.,.5+epsilon),1.])))
        for p in probabilities:
            if epsilon==0:
                value=1.;K=np.sqrt(p)*I2
            elif p<=2*epsilon:
                value=3.
                K=np.diag([np.sqrt(p/(2*(1-epsilon))),np.sqrt(p/(2*epsilon))])
            else:
                value=1+8*epsilon*(p-epsilon)/p**2
                K=np.diag([np.sqrt((p-epsilon)/(1-epsilon)),1.])
            op=np.kron(K,I2);output=op@rho@op.conj().T
            actual_p=np.trace(output).real;output/=actual_p
            actual_value=np.sum(bloch(output)[2]**2)
            max_formula_error=max(max_formula_error,abs(value-actual_value))
            max_probability_error=max(max_probability_error,abs(p-actual_p))
            assert abs(value-actual_value)<2e-12
            assert min(eigvalsh(I2-K.conj().T@K))>-2e-12
            if epsilon:
                a,c,S,W,tau,H,g=canonical_density(rho)
                answer=lens_maximum(tau,H,g,a,p)
                max_lens_error=max(max_lens_error,abs(answer['value']-value))
                assert abs(answer['value']-value)<3e-9
            cases+=1
    return {'Schmidt_epsilon_values':[0.,1e-4,.01,.1,.25,.5],
        'cases':cases,'max_direct_filtering_squared_F3_error':max_formula_error,
        'max_lens_evaluator_squared_F3_error':max_lens_error,
        'max_direct_probability_error':max_probability_error,'all_passed':True}


@dataclass
class Family:
    lam: float
    z0: np.ndarray
    kernel: np.ndarray
    null_radius: float
    kind: str


def sphere_stationary_families(H, g, radius):
    """All stationary multiplier families on a sphere, including hard poles.

    Crucially this returns ALL real secular roots, not only the greatest.
    Radius is positive.  The matrix dimension can be two or three.
    """
    H = (H + H.T) / 2
    n = len(g)
    h, U = eigh(H)
    w = U.T @ g
    scale = max(1.0, norm(H), norm(g) / radius)
    threshold = 2e-10 * scale
    M = np.block([[H, np.eye(n)], [np.outer(g, g) / radius**2, H]])
    roots = eigvals(M)
    real = sorted(float(z.real) for z in roots if abs(z.imag) <= 1e-7 * scale)
    families = []
    used = []
    for lam0 in real:
        if any(abs(lam0 - z) <= 2e-8 * scale for z in used):
            continue
        if min(abs(lam0 - h)) <= 1e-7 * scale:
            continue  # compatible poles are treated explicitly below
        lam = lam0
        for _ in range(4):
            denom = lam - h
            if min(abs(denom)) <= threshold:
                break
            sec = np.sum((w / denom)**2) - radius**2
            derivative = -2 * np.sum(w**2 / denom**3)
            if abs(derivative) < 1e-14:
                break
            step = sec / derivative
            if abs(step) > .02 * scale:
                break
            lam -= step
        denom = lam - h
        if min(abs(denom)) <= threshold:
            continue
        z0 = U @ (w / denom)
        if abs(z0 @ z0 - radius**2) > 1e-6 * max(1., radius**2):
            continue
        families.append(Family(lam, z0, np.zeros((n, 0)), 0., 'regular'))
        used.append(lam)
    seen_eigenvalues = []
    for lam in h:
        if any(abs(lam - z) <= threshold for z in seen_eigenvalues):
            continue
        seen_eigenvalues.append(lam)
        mask = abs(h - lam) <= threshold
        if norm(w[mask]) > threshold:
            continue
        coeff = np.zeros(n)
        coeff[~mask] = w[~mask] / (lam - h[~mask])
        z0 = U @ coeff
        remaining = radius**2 - z0 @ z0
        if remaining < -1e-8 * max(1., radius**2):
            continue
        families.append(Family(float(lam), z0, U[:, mask],
                               float(np.sqrt(max(0., remaining))), 'singular'))
    return families


def family_witness(family, center, other_center=None, other_radius=None):
    """Find the member closest to the other ball, with an explicit formula."""
    x0 = center + family.z0
    K = family.kernel
    r = family.null_radius
    if K.shape[1] == 0 or r == 0:
        x = x0
    elif other_center is None:
        x = x0 + r * K[:, 0]
    else:
        proj = K.T @ (x0 - other_center)
        length = norm(proj)
        if length > 1e-14:
            x = x0 - r * (K @ proj) / length
        else:
            x = x0 + r * K[:, 0]
    if other_center is not None:
        if norm(x - other_center) > other_radius + EPS * max(1., other_radius):
            return None
    return x


def affine_stationary_witness(H, g, centers, radii):
    """Feasibility of stationary affine space via projected balls.

    Supports one ball or two balls.  In the lens case there are two.
    """
    h, U = eigh((H + H.T) / 2)
    threshold = 2e-10 * max(1., norm(H), norm(g))
    mask = abs(h) <= threshold
    w = U.T @ g
    if norm(w[mask]) > threshold:
        return None
    coeff = np.zeros(len(g))
    coeff[~mask] = -w[~mask] / h[~mask]
    x0 = U @ coeff
    K = U[:, mask]
    projected_centers, projected_radii = [], []
    for center, radius in zip(centers, radii):
        k = K.T @ (center - x0)
        perpendicular = x0 - center + K @ k
        rad2 = radius**2 - perpendicular @ perpendicular
        if rad2 < -EPS * max(1., radius**2):
            return None
        projected_centers.append(k)
        projected_radii.append(np.sqrt(max(0., rad2)))
    if len(centers) == 1:
        v = projected_centers[0]
    else:
        k0, k1 = projected_centers
        r0, r1 = projected_radii
        diff = k1 - k0
        distance = norm(diff)
        if distance > r0 + r1 + EPS:
            return None
        if distance > 0:
            v = k0 + min(1., r0 / distance) * diff
        else:
            v = k0
    x = x0 + K @ v
    if any(norm(x - c) > r + 5*EPS*max(1., r) for c, r in zip(centers, radii)):
        return None
    return x


def ball_maximum(tau, H, g, center, radius):
    if radius == 0:
        return {'value': quadratic(tau, H, g, center), 'x': center,
                'source': 'point', 'candidate_count': 1}
    candidates = []
    interior = affine_stationary_witness(H, g, [center], [radius])
    if interior is not None:
        candidates.append((quadratic(tau, H, g, interior), interior, 'stationary-affine'))
    gb = g + H @ center
    for family in sphere_stationary_families(H, gb, radius):
        x = family_witness(family, center)
        candidates.append((quadratic(tau, H, g, x), x, 'sphere-' + family.kind))
    if not candidates:
        raise ArithmeticError('No numerically resolved stationary candidate')
    value, x, source = max(candidates, key=lambda c: c[0])
    return {'value': value, 'x': x, 'source': source, 'candidate_count': len(candidates)}


def circle_maximum(tau, H, g, a, p):
    length = norm(a)
    hplane = 1 - (1 - length**2) / (2*p)
    center = hplane * a / length**2
    rad2 = 1 - center @ center
    if rad2 < -EPS:
        return None
    radius = np.sqrt(max(0., rad2))
    if radius == 0:
        return {'value':quadratic(tau,H,g,center),'x':center,'source':'circle-point'}
    n = a / length
    seed = np.eye(3)[np.argmin(abs(n))]
    e1 = seed - n*(n@seed)
    e1 /= norm(e1)
    e2 = np.cross(n,e1)
    U = np.column_stack([e1,e2])
    H2 = U.T @ H @ U
    g2 = U.T @ (g + H @ center)
    families = sphere_stationary_families(H2,g2,radius)
    if not families:
        raise ArithmeticError('No circle stationary point resolved')
    # The greatest real multiplier is the global equality-sphere solution.
    family = max(families,key=lambda f:f.lam)
    y = family_witness(family,np.zeros(2))
    x = center + U@y
    return {'value':quadratic(tau,H,g,x),'x':x,'source':'intersection-circle'}


def lens_maximum(tau,H,g,a,p):
    """Exact finite-candidate prescription, evaluated in floating point.

    q(x)=tau+2g.x+x.H.x, ||x||<=1, ||a-p*x||<=1-p.
    Assumes ||a||<1 and 0<p<=1.  The physical one-sided F3 reduction uses
    H=S S^T+(||c||^2-tr(S S^T))I and g=S c.
    """
    if not (0 < p <= 1) or norm(a) >= 1:
        raise ValueError('Require mixed marginal and 0<p<=1')
    if p == 1:
        return {'value':quadratic(tau,H,g,a),'x':a.copy(),'source':'probability-one',
                'candidate_count':1,'regime':'high'}
    alen=norm(a)
    if p <= (1-alen)/2:
        ans=ball_maximum(tau,H,g,np.zeros(3),1.)
        ans['regime']='low'
        return ans
    center=a/p
    radius=(1-p)/p
    if p >= (1+alen)/2:
        ans=ball_maximum(tau,H,g,center,radius)
        ans['regime']='high'
        return ans
    centers=[np.zeros(3),center]
    radii=[1.,radius]
    candidates=[]
    interior=affine_stationary_witness(H,g,centers,radii)
    if interior is not None:
        candidates.append((quadratic(tau,H,g,interior),interior,'stationary-affine'))
    for i in [0,1]:
        gb=g+H@centers[i]
        for family in sphere_stationary_families(H,gb,radii[i]):
            x=family_witness(family,centers[i],centers[1-i],radii[1-i])
            if x is not None:
                candidates.append((quadratic(tau,H,g,x),x,f'sphere-{i}-{family.kind}'))
    circle=circle_maximum(tau,H,g,a,p)
    if circle is not None:
        candidates.append((circle['value'],circle['x'],circle['source']))
    if not candidates:
        raise ArithmeticError('No feasible lens candidate was resolved')
    value,x,source=max(candidates,key=lambda c:c[0])
    assert norm(x) <= 1+2e-6
    assert norm(a-p*x) <= 1-p+2e-6
    return {'value':value,'x':x,'source':source,'candidate_count':len(candidates),'regime':'middle'}


def direct_optimize(tau,H,g,a,p,rng):
    constraints=[{'type':'ineq','fun':lambda x:1-x@x},
                 {'type':'ineq','fun':lambda x:(1-p)**2-norm(a-p*x)**2}]
    starts=[a,np.zeros(3)]
    starts.extend(rng.normal(size=3) * rng.uniform(0,.8) for _ in range(5))
    best=-float('inf')
    successes=0
    for start in starts:
        result=minimize(lambda x:-quadratic(tau,H,g,x),start,method='SLSQP',
                        jac=lambda x:-2*(g+H@x),constraints=constraints,
                        options={'ftol':1e-12,'maxiter':800})
        if result.success and norm(result.x)<=1+1e-6 and norm(a-p*result.x)<=1-p+1e-6:
            successes+=1
            best=max(best,-float(result.fun))
    if not np.isfinite(best):
        raise ArithmeticError('All reference optimization starts failed')
    return best,successes


def bloch(rho):
    a=np.array([np.trace(rho@np.kron(s,I2)).real for s in SIGMA])
    b=np.array([np.trace(rho@np.kron(I2,s)).real for s in SIGMA])
    T=np.array([[np.trace(rho@np.kron(s,t)).real for t in SIGMA] for s in SIGMA])
    return a,b,T


def positive_power(M,power):
    vals,U=eigh((M+M.conj().T)/2)
    if power<0 and min(vals)<=0:
        raise ArithmeticError('Higher precision or pure marginal branch required')
    return (U*np.maximum(vals,0)**power)@U.conj().T


def canonical_density(rho):
    tensor=rho.reshape(2,2,2,2)
    rhoA=np.trace(tensor,axis1=1,axis2=3)
    a=np.array([np.trace(rhoA@s).real for s in SIGMA])
    W=positive_power(2*rhoA,-.5)
    big=np.kron(W,I2)
    can=big@rho@big.conj().T
    can/=np.trace(can)
    aa,c,S=bloch(can)
    assert norm(aa)<1e-9
    tau=float(np.sum(S*S))
    H=S@S.T+(c@c-tau)*np.eye(3)
    g=S@c
    return a,c,S,W,tau,H,g


def exact_nonglobal_example():
    a=F(-15,17); p=F(10,51); center=a/p; radius=(1-p)/p
    assert center==F(-9,2) and radius==F(41,10)
    c=F(1,10); s=[F(3,10),F(1,20),F(1,50)]
    assert c+sum(s)==F(47,100)<1
    tau=sum(v*v for v in s)
    H=[v*v+c*c-tau for v in s]
    g=s[0]*c
    original_b=c+s[0]*a
    original_T=[s[0]+a*c,F(8,17)*s[1],F(8,17)*s[2]]
    assert original_b==F(-14,85)
    assert original_T==[F(18,85),F(2,85),F(4,425)]
    x=center+radius
    assert x==F(-2,5)
    V=tau+2*g*x+H[0]*x*x
    assert V==F(17509,250000)
    assert H[0]>0 and H[1]<0 and H[2]<0
    assert 2*g-2*H[0]>0 # q increases in x1 throughout [-1,-2/5]
    gb=g+H[0]*center
    lam=H[0]+gb/radius
    assert lam==F(679,102500)>0
    assert gb<0 # the full second-sphere global maximum is the OTHER pole
    assert H[1]<lam and H[2]<lam # strict tangent local maximum at near pole
    far=center-radius
    assert far==F(-43,5) and far*far>1
    assert (F(1)-center)**2>radius**2 # first-sphere global max infeasible
    circle_x=(radius**2-1-center**2)/(-2*center)
    assert circle_x==F(-37,75)
    circle_value=tau+2*g*circle_x+H[0]*circle_x**2+H[1]*(1-circle_x**2)
    assert circle_value<V
    stationary=-g/H[0]
    assert abs(stationary)>1
    return {'all_fraction_assertions_passed':True,'a':[str(a),'0','0'],
            'b':[str(original_b),'0','0'],'T_diagonal':[str(t) for t in original_T],
            'minimum_success_probability':str(p),'optimal_canonical_x':[str(x),'0','0'],
            'optimal_squared_F3':str(V),'positive_nonglobal_multiplier':str(lam),
            'circle_max_squared_F3':str(circle_value),
            'full_second_sphere_global_x':[str(far),'0','0'],
            'canonical_positivity_norm_upper_bound':str(c+sum(s))}


def main():
    rng=np.random.default_rng(2026110302)
    max_gap=0.; max_excess=0.; max_recovery=0.; max_probability=0.; min_effect_eig=0.
    source_counts={}; regimes={}; total=0; successful_starts=0
    for rank in [1,2,3,4]:
        for _ in range(12):
            Z=rng.normal(size=(4,rank))+1j*rng.normal(size=(4,rank))
            rho=Z@Z.conj().T;rho/=np.trace(rho)
            a,c,S,W,tau,H,g=canonical_density(rho)
            alen=norm(a)
            lo=(1-alen)/2;hi=(1+alen)/2
            probs=[max(.001,lo*.7),lo+(hi-lo)*rng.uniform(.2,.8),hi+(1-hi)*.5]
            for p in probs:
                out=lens_maximum(tau,H,g,a,p)
                ref,nstarts=direct_optimize(tau,H,g,a,p,rng)
                max_gap=max(max_gap,abs(out['value']-ref));max_excess=max(max_excess,ref-out['value'])
                successful_starts+=nstarts;total+=1
                source_counts[out['source']]=source_counts.get(out['source'],0)+1
                regimes[out['regime']]=regimes.get(out['regime'],0)+1
                assert ref<=out['value']+2e-6, (out,ref)
                assert out['value']-ref<2e-5, (out,ref)
                x=out['x']
                E=I2+np.einsum('i,ijk->jk',x,SIGMA)
                K=np.sqrt(p)*positive_power(E,.5)@W
                op=np.kron(K,I2)
                filtered=op@rho@op.conj().T
                probability=np.trace(filtered).real
                filtered/=probability
                actual=np.sum(bloch(filtered)[2]**2)
                max_recovery=max(max_recovery,abs(actual-out['value']))
                max_probability=max(max_probability,abs(probability-p))
                min_effect_eig=min(min_effect_eig,min(eigvalsh(I2-K.conj().T@K)))
                assert abs(actual-out['value'])<2e-7
                assert min(eigvalsh(I2-K.conj().T@K))>-2e-6
    # Structured singular and nonglobal cases, independent of random genericity.
    exact=exact_nonglobal_example()
    tau=float(F(929,10000));H=np.diag([float(F(71,10000)),float(F(-201,2500)),float(F(-33,400))])
    g=np.array([.03,0.,0.]);a=np.array([-15/17,0.,0.]);p=10/51
    out=lens_maximum(tau,H,g,a,p)
    assert abs(out['value']-float(F(17509,250000)))<1e-12
    assert norm(out['x']-np.array([-.4,0,0]))<1e-10
    assert out['source']=='sphere-1-regular'
    structured=[]
    for HH,gg,aa,pp in [
      (np.zeros((3,3)),np.zeros(3),np.array([.4,0,0]),.5),
      (np.diag([0.,-1.,-2.]),np.array([0.,.1,0]),np.array([0.,.5,0]),.5),
      (np.diag([1.,1.,-1.]),np.array([0.,0.,.1]),np.array([.5,0.,0]),.6),
      (np.eye(3),np.zeros(3),np.array([0.,0.,.4]),.5),
      (-np.eye(3),np.zeros(3),np.array([.2,0.,0.]),.95),
    ]:
        ans=lens_maximum(0.,HH,gg,aa,pp)
        reference,nstarts=direct_optimize(0.,HH,gg,aa,pp,rng)
        assert abs(ans['value']-reference)<2e-6
        structured.append({'value':ans['value'],'source':ans['source'],'regime':ans['regime'],
                           'reference_gap':abs(ans['value']-reference)})
    result={'seed':2026110302,'physical_states':48,'density_ranks':[1,2,3,4],
       'probability_constrained_cases':total,'regimes':regimes,'winning_candidates':source_counts,
       'successful_reference_starts':successful_starts,'reference_starts_total':total*7,
       'max_absolute_optimizer_gap':max_gap,'max_optimizer_excess_over_formula':max_excess,
       'max_direct_filtered_F3_squared_error':max_recovery,
       'max_direct_success_probability_error':max_probability,
       'minimum_I_minus_effect_eigenvalue':min_effect_eig,
       'exact_nonglobal_sphere_example':exact,'structured_singular_checks':structured,
       'best_success_optimal_family_checks':best_success_checks(),
       'pure_state_frontier_checks':pure_state_frontier_checks(),
       'all_passed':True,'scope':'Float64 implementation checks plus a separate exact Fraction example; not a Lean proof.'}
    Path(__file__).with_name('extension_results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__':
    main()
