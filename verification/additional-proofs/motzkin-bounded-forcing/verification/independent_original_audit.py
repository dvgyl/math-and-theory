#!/usr/bin/env python3
"""Independent symbolic cross-check using SymPy, not a formal proof assistant."""
import json
import sympy as s
from math import comb
n,r,e=s.symbols('n r e')
m=n+3
L=3-s.Rational(9,2)/m+s.Rational(9,16)/m**2
U=L+2/m**3
E=1/(8*m**2)
f=lambda r,e:(n+1)/(n+3)*(2+3/r)+2*e/(n+3)
pl=304*n**3+1687*n**2+1599*n-1790
pu=112*n**2-509*n-1331
checks={}
checks['lower_envelope_identity']=s.cancel(f(U.subs(n,n-1),-E)-L-pl/(16*m**3*(48*n**3+216*n**2+297*n+146)))==0
checks['upper_envelope_identity']=s.cancel(U-f(L.subs(n,n-1),E)-pu/(16*m**3*(16*n**2+40*n+19)))==0
y=((n+2)*(2*r+3)+2*e)/(n+4)
z=((n+3)*(2*y+3*r)-2*e)/(n+5)
F=y**3-r**3*z
checks['derivative_e_identity']=s.cancel(s.diff(F,e)-(6*(n+5)*y*y-2*(n+2)*r**3)/((n+4)*(n+5)))==0
checks['derivative_r_identity']=s.cancel(s.diff(F,r)-(3*y*y*s.diff(y,r)-3*r*r*z-r**3*s.diff(z,r)))==0
P=s.Poly(s.cancel(F.subs({r:U,e:-E})*65536*m**11*(n+4)**3*(n+5)),n)
expected=[111034368,3364180992,46409331456,385445807712,2146478817312,8443039471929,24049942325892,49975719381810,75163688028504,79753800966621,56628081108524,24132003073520,4660409556032]
checks['positive_polynomial_identity']=P.all_coeffs()==expected
b0,b1,b2,b3=s.symbols('b0 b1 b2 b3')
Dn=2*(n*n-1)*b1-n*(n+1)*b0-n*(n-1)*b2
Dn1=2*((n+1)**2-1)*b2-(n+1)*(n+2)*b1-(n+1)*n*b3
checks['log_transfer_identity']=s.expand(Dn1-Dn-n*(n+1)*(b0-3*b1+3*b2-b3))==0
# Independently produce finite Motzkin values from the binomial-Catalan sum.
M=[sum(comb(k,2*j)*(comb(2*j,j)//(j+1)) for j in range(k//2+1)) for k in range(36)]
T=[sum((-1)**(k-j)*M[j] for j in range(k+1)) for k in range(36)]
checks['finite_motzkin_recurrence']=all((k+3)*M[k+1]==(2*k+3)*M[k]+3*k*M[k-1] for k in range(1,35))
checks['finite_T_recurrence']=all((k+2)*T[k]==k*(2*T[k-1]+3*T[k-2])+2*(-1)**k for k in range(2,36))
checks['root_bases']=all(T[k]**(2*(k*k-1))>T[k-1]**(k*(k+1))*T[k+1]**(k*(k-1)) for k in range(6,12))
checks['root_sharpness']=T[5]**24<T[4]**15*T[6]**10
checks['ratio_bases']=all(T[k]*T[k+2]**3>T[k+1]**3*T[k+3] for k in [10,11])
checks['ratio_sharpness']=T[9]*T[11]**3<T[10]**3*T[12]
if not all(checks.values()):
    raise RuntimeError({k:v for k,v in checks.items() if not v})
print(json.dumps({'status':'all_independent_checks_passed','sympy_version':s.__version__,'checks':checks,'lean_verified':False},indent=2))
