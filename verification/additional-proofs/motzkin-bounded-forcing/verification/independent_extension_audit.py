#!/usr/bin/env python3
"""Independent SymPy audit. Does not import the custom polynomial checker."""
from __future__ import annotations
import argparse
import json
from math import comb
from pathlib import Path
import sympy as sp


def audit(certificate_file: Path) -> dict:
    d = json.loads(certificate_file.read_text())
    checks = []
    def require(name, condition):
        if not bool(condition):
            raise ArithmeticError(name)
        checks.append(name)
    n, r, u, v, s = sp.symbols('n r u v s')
    L = lambda k: 3-sp.Rational(9,2)/(k+3)+sp.Rational(9,16)/(k+3)**2
    U = lambda k: L(k)+2/(k+3)**3
    E = lambda k: 1/(8*(k+3)**2)
    f = lambda k,x,e: (k+1)/(k+3)*(2+3/x)+2*e/(k+3)
    P = sum(sp.Integer(c)*n**j for j,c in enumerate(d['P']))
    lo = sum(sp.Integer(c)*n**j for j,c in enumerate(d['envelope_lower_numerator']))
    hi = sum(sp.Integer(c)*n**j for j,c in enumerate(d['envelope_upper_numerator']))
    require('lower rational envelope identity', sp.cancel(f(n,U(n-1),-E(n))-L(n)
        -lo/(16*(n+3)**3*(48*n**3+216*n**2+297*n+146)))==0)
    require('upper rational envelope identity', sp.cancel(U(n)-f(n,L(n-1),E(n))
        -hi/(16*(n+3)**3*(16*n**2+40*n+19)))==0)
    y = ((n+2)*(2*r+3)+2*u)/(n+4)
    z = ((n+3)*(2*y+3*r)+2*v)/(n+5)
    F = y**3-r**3*z
    require('corner rational identity', sp.cancel(F.subs({r:U(n),u:-E(n),v:E(n)})
        -P/(65536*(n+3)**11*(n+4)**3*(n+5)))==0)
    poly = sp.Poly(sp.expand((P-800*65536*(n+3)**8*(n+4)**3*(n+5)).subs(n,n+12)),n)
    require('quantitative coefficients independently expanded',
            list(reversed(poly.all_coeffs()))==d['quantitative_shift_at_12'])
    require('quantitative coefficient positivity', all(c>0 for c in poly.all_coeffs()))
    require('independent r derivative', sp.cancel(sp.diff(F,r)
        -(3*y*y*(2*(n+2)/(n+4))-3*r*r*z-r**3*(n+3)*(7*n+20)/((n+4)*(n+5))))==0)
    require('independent u derivative', sp.cancel(sp.diff(F,u)
        -(2/(n+4))*(3*y*y-2*(n+3)/(n+5)*r**3))==0)
    require('independent v derivative', sp.cancel(sp.diff(F,v)+2*r**3/(n+5))==0)
    # A different construction of M: finite Catalan/binomial sum, not recurrence.
    M = [sum(comb(k,2*j)*comb(2*j,j)//(j+1) for j in range(k//2+1)) for k in range(20)]
    T = [sum((-1)**(k-j)*M[j] for j in range(k+1)) for k in range(20)]
    require('finite values via Catalan sum',T[:16]==d['T_0_through_15'])
    A = lambda k: sp.Integer(T[k])+(s-1)*(-1)**k
    for k in range(2,12):
        q = sp.Poly(A(k)*A(k+2)**3-A(k+1)**3*A(k+3),s)
        require(f'family cubic Q_{k}', list(reversed(q.all_coeffs()))==d['family_ratio_polynomials'][str(k)])
    den=sp.Integer(d['isolating_denominator'])
    for name in ['ratio_root_brackets','root_gap_root_brackets']:
        for key,pair in d[name].items():
            k=int(key)
            p=(A(k)*A(k+2)**3-A(k+1)**3*A(k+3)) if name=='ratio_root_brackets' else (
                A(k)**(k*k-1)-A(k-1)**(k*(k+1)//2)*A(k+1)**(k*(k-1)//2))
            lv,hv=[p.subs(s,sp.Rational(x,den)) for x in pair]
            require(f'exact independent signs {name}:{k}',lv<0<hv if k%2==0 else lv>0>hv)
    for k in range(6,12):
        p=A(k)**(k*k-1)-A(k-1)**(k*(k+1)//2)*A(k+1)**(k*(k-1)//2)
        require(f'family root base {k}',p.subs(s,k%2)>0)
    require('root boundary tau2 factor',sp.expand(A(2)**3-A(1)**3*A(3)
        +(s*s-6*s+1)*(s*s-s+2))==0)
    return {'status':'passed','sympy_version':sp.__version__,'independent_check_count':len(checks),
        'checks':checks,'floating_point_used':False,'lean_verified':False,
        'scope':'Independent symbolic identities and finite exact arithmetic, not a proof-assistant verification.'}

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--certificates',type=Path,default=Path(__file__).resolve().parents[1]/'proof/certificates.json')
    p.add_argument('--output',type=Path)
    args=p.parse_args()
    text=json.dumps(audit(args.certificates),indent=2)+'\n'
    if args.output: args.output.write_text(text)
    else: print(text,end='')
