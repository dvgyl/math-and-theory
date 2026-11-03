#!/usr/bin/env python3
"""Exact fixtures and falsification checks for collective coupling capacity.

Universal results are proved in collective_capacity.tex. Numerical samples,
asymptotic comparisons and scalar optimization are diagnostics, not proofs.
"""
from pathlib import Path
from itertools import product
import json
import math
import numpy as np
import sympy as sp
from scipy.optimize import minimize_scalar
from scipy.special import gammaln, logsumexp

OUT = Path(__file__).resolve().with_name('collective_capacity_results.json')
rng = np.random.default_rng(2026110302)


def capacity(a, b, p, n):
    u, v = np.sqrt(np.asarray(a)*p), np.sqrt(np.asarray(b)*p)
    lu, lv = np.log(u), np.log(v)
    logs = [min(sum(lu[i] for i in seq), sum(lv[i] for i in seq))
            for seq in product(range(len(a)), repeat=n)]
    return float(np.exp(2*logsumexp(logs)))


def coefficient_data(a, b, p):
    u, v = np.sqrt(np.asarray(a)*p), np.sqrt(np.asarray(b)*p)
    lu, lv = np.log(u), np.log(v)
    z = lambda t: float(np.sum(np.exp(t*lu+(1-t)*lv)))
    sol = minimize_scalar(z, bounds=(0.,1.), method='bounded',
                          options={'xatol':1e-13})
    t = min([0.,float(sol.x),1.], key=z)
    kappa = z(t)
    q = np.exp(t*lu+(1-t)*lv)/kappa
    mu = float(q@(lu-lv))
    variance = float(q@((lu-lv-mu)**2))
    return t, kappa, mu, variance


def coherent_min(a, b):
    a, b = np.asarray(a), np.asarray(b)
    m = np.minimum(a,b)
    z = np.diag(np.sqrt(m)).reshape(-1)
    rho = np.outer(z,z)
    delta = 1.-np.sum(m)
    if delta > 1e-14:
        rho += np.diag(np.kron(a-m,b-m)/delta)
    return rho


def partials(rho, d):
    t = rho.reshape(d,d,d,d)
    return np.einsum('ijkj->ik', t), np.einsum('ijil->jl', t)


# Exact two-copy state and independently evaluated objective/marginals.
a2 = [sp.Rational(x,100) for x in (49,21,21,9)]
b2 = list(reversed(a2))
z = sp.zeros(16,1)
for i,t in enumerate((3,sp.sqrt(21),sp.sqrt(21),3)):
    z[5*i] = sp.sympify(t)/10
rho = z*z.T
rho[3,3] += sp.Rational(2,5)
phi = sp.zeros(16,1)
for i in range(4):
    phi[5*i] = sp.Rational(1,2)
ra = sp.Matrix(4,4,lambda i,k: sum(rho[4*i+j,4*k+j] for j in range(4)))
rb = sp.Matrix(4,4,lambda j,l: sum(rho[4*i+j,4*i+l] for i in range(4)))
assert ra == sp.diag(*a2) and rb == sp.diag(*b2)
assert sp.trace(rho)==1 and rho.rank()==2
two = (15+3*sp.sqrt(21))/50
assert sp.simplify((phi.T*rho*phi)[0]-two)==0
assert sp.simplify(two-sp.Rational(9,25))>0
three=(297+27*sp.sqrt(21))/1000
root_difference=(2349*sp.sqrt(21)-4239)/500000
assert sp.simplify(two**3-three**2-root_difference)==0
assert root_difference>0
exact_eigenvalues = rho.eigenvals()
assert exact_eigenvalues == {sp.Rational(3,5):1,sp.Rational(2,5):1,0:14}

random_records=[]
max_sandwich_excess=0.
max_super_excess=0.
min_strict_gap=math.inf
max_mu_error=0.
actual_checks=0
max_actual_error=0.
endpoint_counts={'left':0,'interior':0,'right':0}
for d in (2,3,4):
    for case in range(40):
        a,b,p = rng.dirichlet(np.ones(d),size=3)
        vals={n:capacity(a,b,p,n) for n in range(1,5)}
        t,kappa,mu,variance=coefficient_data(a,b,p)
        category='left' if t==0 else 'right' if t==1 else 'interior'
        endpoint_counts[category]+=1
        if category=='interior':
            max_mu_error=max(max_mu_error,abs(mu))
        elif category=='left':
            assert mu>=-1e-10
        else:
            assert mu<=1e-10
        for n in vals:
            upper=kappa**(2*n)
            lower=.25*math.exp(-2*math.sqrt(2*n*variance))*upper
            max_sandwich_excess=max(max_sandwich_excess,vals[n]-upper,lower-vals[n])
            assert vals[n]<=upper+3e-12
            assert vals[n]>=lower-3e-12
        for n,m in ((1,1),(1,2),(2,2)):
            gap=vals[n+m]-vals[n]*vals[m]
            min_strict_gap=min(min_strict_gap,gap)
            max_super_excess=max(max_super_excess,-gap)
            assert gap>0
        assert kappa*kappa>vals[1]
        # Check full density, traces and target for the one-copy attaining state.
        state=coherent_min(a,b)
        aa,bb=partials(state,d)
        target=np.diag(np.sqrt(p)).reshape(-1)
        err=max(np.max(np.abs(aa-np.diag(a))),np.max(np.abs(bb-np.diag(b))),
                abs(float(target@state@target)-vals[1]),abs(np.trace(state)-1),
                max(0.,-float(np.linalg.eigvalsh(state).min())))
        max_actual_error=max(max_actual_error,float(err))
        actual_checks+=1
        assert err<3e-13
        random_records.append({'d':d,'case':case,'t_star':t,'kappa_squared':kappa*kappa,
                               'capacities':vals,'sigma_squared':variance})

# A target concentrated on one sign of log(a/b) forces a boundary minimum.
endpoint_fixtures=[]
for a,b,p in [([.8,.2],[.4,.6],[.999,.001]),
              ([.8,.2],[.4,.6],[.001,.999])]:
    t,kappa,mu,var=coefficient_data(a,b,p)
    endpoint_fixtures.append({'t_star':t,'mu':mu,'rate':kappa*kappa})
assert endpoint_fixtures[0]['t_star']==0.
assert endpoint_fixtures[1]['t_star']==1.

# The equal-marginal boundary is exactly multiplicative.
equal_errors=[]
for d in (2,3,4):
    a,p=rng.dirichlet(np.ones(d),size=2)
    one=capacity(a,a,p,1)
    for n in range(1,5):
        equal_errors.append(abs(capacity(a,a,p,n)-one**n))
assert max(equal_errors)<1e-13


def binary_log_capacity(t,n):
    k=np.arange(n+1,dtype=float)
    log_mass=gammaln(n+1)-gammaln(k+1)-gammaln(n-k+1)-n*math.log(2.)
    logr=.5*math.log((1-t)/t)
    log_expect=float(logsumexp(log_mass+abs(k-n/2)*logr))
    return n*math.log(2*math.sqrt(t*(1-t)))+2*log_expect


# Test the independent binomial expression and its parity constants.
binary_checks=0
asymptotic=[]
for t in (.55,.7,.85,.95):
    for n in range(1,9):
        direct=capacity([t,1-t],[1-t,t],[.5,.5],n)
        assert abs(direct-math.exp(binary_log_capacity(t,n)))<3e-13
        binary_checks+=1
    r=math.sqrt((1-t)/t)
    lam=2*math.sqrt(t*(1-t))
    for n in (200,201,2000,2001,20000,20001,100000,100001):
        weight=(1+r)/(1-r) if n%2==0 else 2*math.sqrt(r)/(1-r)
        log_equivalent=n*math.log(lam)+math.log(2/(math.pi*n))+2*math.log(weight)
        ratio=math.exp(binary_log_capacity(t,n)-log_equivalent)
        assert 0<ratio<1.001
        asymptotic.append({'t':t,'n':n,'ratio_to_parity_equivalent':ratio})
    # Convergence is slow as t tends to 1/2; keep the visible finite-size error.
    assert all(abs(z['ratio_to_parity_equivalent']-1)<.01
               for z in asymptotic if z['t']==t and z['n']>=100000)

# Zero-support strictness tests use direct products without logarithms.
def capacity_with_zeros(a,b,p,n):
    total=0.
    for seq in product(range(len(a)),repeat=n):
        aa=math.prod(a[i] for i in seq)
        bb=math.prod(b[i] for i in seq)
        pp=math.prod(p[i] for i in seq)
        total+=math.sqrt(pp*min(aa,bb))
    return total**2

zero_fixtures=[]
for a,b,p in [([.6,.4,0],[.3,.3,.4],[.2,.5,.3]),
              ([.8,.2,0],[.1,.6,.3],[.2,.5,.3]),
              ([1,0,0],[0,1,0],[.2,.5,.3]),
              ([.8,.2,0],[.1,.6,.3],[1,0,0])]:
    I=[i for i in range(len(a)) if p[i]*a[i]*b[i]>0]
    crosses=any(a[i]>b[i] for i in I) and any(a[i]<b[i] for i in I)
    c1=capacity_with_zeros(a,b,p,1)
    c2=capacity_with_zeros(a,b,p,2)
    if crosses:
        assert c2>c1*c1+1e-12
    else:
        assert abs(c2-c1*c1)<1e-13
    zero_fixtures.append({'active_support':I,'crosses':crosses,'C1':c1,'C2':c2})

report={
    'all_passed':True,
    'scope':'Exact SymPy fixture plus seeded numerical and asymptotic diagnostics; not universal proof.',
    'seed':2026110302,
    'exact_fixture':{'C1':'3/5','C2':str(two),'C3':str(three),
                     'C2_cubed_minus_C3_squared':str(root_difference),'rate':'sqrt(21)/5',
                     'state_rank':2,'eigenvalues':{'3/5':1,'2/5':1,'0':14}},
    'random_triples':len(random_records),
    'finite_capacity_checks':4*len(random_records),
    'strict_supermultiplicativity_checks':3*len(random_records),
    'min_strict_gap':min_strict_gap,
    'max_supermultiplicativity_excess':max_super_excess,
    'max_finite_sandwich_excess':max_sandwich_excess,
    'max_interior_derivative_residual':max_mu_error,
    'actual_density_checks':actual_checks,'max_actual_density_error':max_actual_error,
    'endpoint_counts':endpoint_counts,'endpoint_fixtures':endpoint_fixtures,
    'equal_marginal_checks':len(equal_errors),'max_equal_error':max(equal_errors),
    'binary_exact_formula_diagnostics':binary_checks,
    'parity_asymptotics':asymptotic,'zero_support_fixtures':zero_fixtures,
    'random_records':random_records,
}
OUT.write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k!='random_records'},indent=2))
