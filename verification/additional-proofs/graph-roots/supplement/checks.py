#!/usr/bin/env python3
"""Reproducible checks for book-graph and square-flower domination polynomials.

These are exact finite checks and numerical diagnostics, NOT Lean verification
and NOT replacements for the all-n proofs in the accompanying manuscript.
Dependencies: Python 3.10+, sympy, mpmath.
"""
from __future__ import annotations

if not __debug__:
    raise SystemExit("Verification requires assertions; optimized Python is not supported.")
import argparse
import json
from pathlib import Path
import platform
import shutil
import sys
import sympy as sp
import mpmath as mp

x = sp.Symbol('x')
t = sp.Symbol('t')


def polynomial(family: str, n: int) -> sp.Poly:
    if n < 1:
        raise ValueError('n must be positive')
    if family == 'flower':
        a = x*x + 3*x + 3
        expression = x**n * (x*a**n + (a-2)**n - 1)
    elif family == 'book':
        expression = (2*x+1)*(x*x+2*x)**n + x*x*(1+x)**(2*n)-2*x**n
    else:
        raise ValueError(f'unknown family {family!r}')
    return sp.Poly(expression, x, domain=sp.ZZ)


def graph_masks(family: str, n: int) -> list[int]:
    """Closed neighbourhood masks, built from edges independently of formulas."""
    if family == 'flower':
        count = 3*n+1
        edges = []
        for i in range(n):
            a,b,c = 3*i+1,3*i+2,3*i+3
            edges.extend([(0,a),(a,b),(b,c),(c,0)])
    elif family == 'book':
        count = 2*n+2
        edges = [(0,1)]
        for i in range(n):
            a,b = 2*i+2,2*i+3
            edges.extend([(0,a),(a,b),(b,1)])
    else:
        raise ValueError(f'unknown family {family!r}')
    masks = [1 << i for i in range(count)]
    for a,b in edges:
        masks[a] |= 1 << b
        masks[b] |= 1 << a
    return masks


def enumerate_coefficients(family: str, n: int) -> list[int]:
    masks = graph_masks(family,n)
    count = len(masks)
    if count > 22:
        raise ValueError('exhaustive enumeration capped at 22 vertices')
    full = (1 << count)-1
    covered = [0]*(1 << count)
    coefficients = [0]*(count+1)
    for subset in range(1,1 << count):
        bit = subset & -subset
        covered[subset] = covered[subset ^ bit] | masks[bit.bit_length()-1]
        if covered[subset] == full:
            coefficients[subset.bit_count()] += 1
    return coefficients


def exact_algebra_checks() -> dict:
    n = sp.Symbol('n', integer=True, positive=True)
    e = (1-t)*(2-t)
    log_derivative = 2/t-2*n/(t*e)
    target = 2*(e**2+n*t*(6-t)+2*n*(n-3))/(t*t*e*e)
    assert sp.cancel(sp.diff(log_derivative,t)+log_derivative**2-target) == 0
    def odd_f(n0: int, t0: sp.Rational):
        return sp.cancel(t0**2*((1-t0)**2/(t0*(2-t0)))**n0
                         +2/(2-t0)**n0+2*t0-1)
    assert odd_f(3,sp.Rational(1,5)) == -sp.Rational(589,18225)
    assert odd_f(5,sp.Rational(1,3)) == -sp.Rational(3977,28125)
    a = t*t-3*t+3
    assert sp.expand((a-2)**2-t*a*a-1
                     +(2*t-3)**2+(t-1)*a*a) == 0
    central = sp.Rational(19,16)**4-sp.Rational(3,2)*sp.Rational(13,16)**4-1
    assert central == sp.Rational(43887,131072) and central > 0
    # Formal symbols stand for powers at arbitrary n in the published recurrence.
    U,V,W = sp.symbols('U V W')
    A = x*x+3*x+3
    B = A-2
    recurrence = ((1+4*x+3*x*x+x**3)*(x*U+V-W)
                  -(1+3*x)*V+(1+x)**3*W-(x*x+x)*U)
    next_value = x*(x*A)*U+(x*B)*V-x*W
    assert sp.expand(recurrence-next_value) == 0
    # A reciprocal-coordinate identity used in the asymptotic proof.
    w = sp.Symbol('w')
    ratio = (1+3*w+w*w)/(1+3*w+3*w*w)
    assert sp.series(sp.log(ratio),w,0,4).removeO() == -2*w*w+6*w**3
    return {'book_convexity_identity': True,
            'odd_n3_witness': str(odd_f(3,sp.Rational(1,5))),
            'odd_n5_witness': str(odd_f(5,sp.Rational(1,3))),
            'flower_n2_identity': True,
            'flower_middle_lower_bound': str(central),
            'flower_recurrence_identity': True,
            'reciprocal_log_expansion': '-2*w^2 + 6*w^3 + O(w^4)'}


def exact_real_root_checks(max_n: int) -> list[dict]:
    results=[]
    for family in ['book','flower']:
        for n in range(1,max_n+1):
            p=polynomial(family,n)
            multiplicity=2 if family=='book' else n+1
            q,rem=sp.div(p,sp.Poly(x**multiplicity,x))
            assert rem.is_zero and q.eval(0)!=0
            # Sturm root counting over the rationals; no floating root finder.
            count=int(q.count_roots(-sp.oo,sp.oo))
            expected=(0 if n==1 else 2) if family=='book' else (2 if n>=4 and n%2==0 else 0)
            assert count==expected,(family,n,count,expected)
            # Nonzero roots are simple (in fact this checks all roots of q).
            squarefree = sp.gcd(q,q.diff()).degree()==0
            assert squarefree
            if family=='book' and n%2==0:
                assert q.count_roots(-3,-2)==1
                assert q.count_roots(-sp.Rational(1,2),0)==1
            elif family=='book' and n>=3:
                assert q.count_roots(-sp.Rational(1,2),0)==2
            elif family=='flower' and expected==2:
                assert q.count_roots(-2,-sp.Rational(3,2))==1
                assert q.count_roots(-sp.Rational(5,4),-1)==1
            row={'family':family,'n':n,'zero_multiplicity':multiplicity,
                 'nonzero_real_roots':count,'nonzero_factor_squarefree':squarefree}
            results.append(row)
        print(f'Exact Sturm checks: {family}, n=1..{max_n}: PASS',flush=True)
    return results


def asymptotic_diagnostics() -> list[dict]:
    """Find a large complex root. No assertion that it is the maximum root."""
    mp.mp.dps=90
    rows=[]
    for n in [100,1000,10000,10**6,10**10,10**20]:
        lam=mp.lambertw(-4*n,0)
        w0=-mp.exp(-lam/2)
        def f(v):
            w=w0*(1+v/lam)
            p=1+3*w+3*w*w
            return 1+w*mp.exp(n*mp.log1p(-2*w*w/p))-w*(w*w/p)**n
        v=mp.findroot(f,(mp.mpc(0),mp.mpc('0.01')),tol=mp.mpf('1e-70'),maxsteps=150)
        residual=abs(f(v))
        assert residual<mp.mpf('1e-65'),(n,residual)
        z=1/(w0*(1+v/lam))
        bound=2+mp.sqrt(4*n/mp.lambertw(4*n))
        assert abs(z)<bound
        denom=4*n/abs(z)**2
        target=mp.log(4*n)-mp.log(mp.log(4*n))
        rows.append({'n':n,'root_real':mp.nstr(z.real,24),
                     'root_imag':mp.nstr(z.imag,24),
                     'root_modulus':mp.nstr(abs(z),24),
                     'global_bound':mp.nstr(bound,24),
                     'ratio_to_2sqrt_n_over_logn':mp.nstr(abs(z)/(2*mp.sqrt(n/mp.log(n))),18),
                     'denominator_minus_log4n_plus_loglog4n':mp.nstr(denom-target,18),
                     'normalized_residual':mp.nstr(residual,8),
                     'is_certified_maximum':False})
    print('High-precision asymptotic diagnostics: PASS (numerical, not proof)',flush=True)
    return rows


def main() -> None:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-n',type=int,default=20)
    parser.add_argument('--output',type=Path,default=Path('check_results.json'))
    args=parser.parse_args()
    if not 1<=args.max_n<=50:
        parser.error('--max-n must lie between 1 and 50')
    result={'disclaimer':'Not Lean verification. Exact finite checks plus numerical diagnostics.',
            'python':platform.python_version(),'sympy':sp.__version__,'mpmath':mp.__version__,
            'lean_executable':shutil.which('lean'),'algebra':exact_algebra_checks()}
    print('Exact symbolic identities: PASS',flush=True)
    enumerations=[]
    for family,upper in [('flower',6),('book',8)]:
        for n in range(1,upper+1):
            actual=enumerate_coefficients(family,n)
            p=polynomial(family,n)
            expected=[int(p.nth(k)) for k in range(len(actual))]
            assert actual==expected,(family,n)
            enumerations.append({'family':family,'n':n,'vertices':len(actual)-1,
                                 'subsets_examined':2**(len(actual)-1),'pass':True})
        print(f'Independent graph-set enumeration: {family}, n=1..{upper}: PASS',flush=True)
    result['graph_enumeration']=enumerations
    result['exact_root_checks']=exact_real_root_checks(args.max_n)
    result['asymptotic_diagnostics']=asymptotic_diagnostics()
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(f'Results written to {args.output}',flush=True)

if __name__=='__main__':
    main()
