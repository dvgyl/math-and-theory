#!/usr/bin/env python3
"""Verify the cubic identities with symbolic arithmetic."""
import json
from math import factorial
from pathlib import Path
import sympy as s

x = s.symbols('x0:3')
t = s.symbols('t', real=True)
R = sum(x) / 3


def norm(p):
    return s.expand(sum(s.prod(factorial(k) for k in a) * c * c for a, c in s.Poly(p, *x).terms()))


def deletion_norm(p, j):
    q = s.Poly(p, x[j]).coeff_monomial(x[j])
    y, z = [x[k] for k in range(3) if k != j]
    q = s.Poly(q, y, z)
    a, b, c = [q.coeff_monomial(mon) for mon in [y*y, y*z, z*z]]
    return s.expand(b*b + 4*a*c)


A = s.eye(3)/2 + s.Matrix([[0,1,0],[0,0,1],[1,0,0]])/2
As = s.ones(3)/3 + t*(A-s.ones(3)/3)
p = s.expand(s.prod(sum(As[i,j]*x[j] for j in range(3)) for i in range(3)))
poly = s.Poly(p, *x)
b = s.Rational(2,9)+t*t/12-t**3/18
a = s.Rational(1,9)+t**3/72
assert s.expand(poly.coeff_monomial(s.prod(x))-b) == 0
for i in range(3):
    for j in range(3):
        if i != j:
            assert s.expand(poly.coeff_monomial(x[i]**2*x[j])-a) == 0
Hs = [deletion_norm(p,j) for j in range(3)]
assert all(s.expand(H-b*b-4*a*a) == 0 for H in Hs)
assert s.diff(Hs[0]/(s.Rational(4,9)*norm(p)),t).subs(t,1) == -s.Rational(3,16)
x0,y,z = x
p = s.expand((y+z)*((y+z)**2/(4*s.sqrt(3))+x0*(y+z)/2+x0*x0/s.sqrt(3)))
value = s.simplify(p.subs(dict.fromkeys(x,1)))
assert value == 2+4*s.sqrt(3)/3
assert all(s.simplify(s.diff(p,v).subs(dict.fromkeys(x,1))-value) == 0 for v in x)
assert s.simplify(norm(p)-s.Rational(13,3)) == 0
assert all(s.simplify(deletion_norm(p,j)-2) == 0 for j in range(3))
assert s.simplify(3*sum(deletion_norm(p,j) for j in range(3))-4*norm(p)) == s.Rational(2,3)
U = [s.Poly(p,*x).coeff_monomial(v**3) for v in x]
assert s.simplify(5-24*sum(u*u for u in U)-s.Rational(2,3)) == s.Rational(10,3)
q = x0*(y+z)**2/4
H = s.hessian(s.diff((1-t)*R**3+t*q,x0),x)
assert H == 2*(1-t)*s.ones(3)/9+t*s.Matrix([[0,0,0],[0,1,1],[0,1,1]])/2
report = {'all_checks_passed':True,'arithmetic':'SymPy exact symbolic arithmetic',
          'checks':['uniform mixing coefficients and derivative','Lorentzian mixed-coefficient example','segment Hessian identity']}
Path('cubic-symbolic-results.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report))
