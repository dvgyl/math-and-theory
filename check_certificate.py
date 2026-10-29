#!/usr/bin/env python3
"""Independently expand every integer certificate and reduction identity."""
import json
from pathlib import Path
import sympy as s

def main():
    if not __debug__:
        raise RuntimeError('Optimized Python is unsupported: certificate assertions must run')
    data=json.loads((Path(__file__).parent/'certificate.json').read_text())
    t,z,q,r=s.symbols('t z q r')
    P=sum(s.Integer(c)*t**i for i,c in enumerate(data['polynomial_coefficients']))
    assert s.degree(P,t)==14
    intervals=[]
    for rec in data['intervals']:
        a,b,den=map(s.Integer,(rec['a'],rec['b'],rec['q']))
        cc=list(map(s.Integer,rec['positive_coefficients']))
        scale=s.Integer(rec['scale'])
        assert len(cc)==15 and scale>0 and all(c>0 for c in cc)
        rhs=sum(c*(den*t-a)**j*(b-den*t)**(14-j) for j,c in enumerate(cc))
        assert s.Poly(scale*P-rhs,t).is_zero
        intervals.append((a/den,b/den))
    assert intervals==[(s.Rational(27,50),s.Rational(541,1000)),
        (s.Rational(541,1000),s.Rational(3,5)),(s.Rational(3,5),s.Integer(1))]
    D=lambda x:105-70*x-14*x**2-6*x**3
    R=lambda x,y:2*D(y)*x**2-(1-y)*(D(y)+105)
    F=lambda x,y:48*x**4-32*x**3-24*x**2+8+y*(24*x**2-7)
    E=15+(1-z)*(1-q)*(20+6*(z+q))
    assert s.expand(D(z)*R(t,q)-D(q)*R(t,z)-(q-z)*(D(z)*D(q)+105*E))==0
    B=24*t*t-7
    q0=-(48*t**4-32*t**3-24*t*t+8)/B
    assert s.cancel(B**4*R(t,q0)-2*(t-1)*P)==0
    assert s.expand(F(t,1)-(2*t-1)**2*(12*t*t+4*t+1))==0
    bound=2*r+2*r**3/3+2*r**5/5+2*r**7/(7*(1-r*r))
    assert s.cancel(s.diff(bound-s.log((1+r)/(1-r)),r)-4*r**8/(7*(1-r*r)**2))==0
    print(json.dumps({'all_passed':True,'intervals':[[str(a),str(b)] for a,b in intervals],
       'integer_certificates':len(intervals),'polynomial_identities':4,'sympy':s.__version__},indent=2))
    return 0

if __name__=='__main__': raise SystemExit(main())
