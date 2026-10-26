"""Exact certificate against an averaged Fock-capacity deletion shortcut.

No general Gyires inequality is refuted. Uses Python integers and Fraction only.
"""
from fractions import Fraction
from math import factorial
import hashlib
import json
from pathlib import Path

def certificate(n=700):
    # P = Bernoulli(7/10) + Binomial(n-2, 3/(10*(n-2))).
    # P_k=I_k/D, with one common denominator D.
    M=10*(n-2)
    L=M-3
    base=[L**(n-2)]
    for k in range(n-2):
        numerator=base[-1]*(n-2-k)*3
        denominator=(k+1)*L
        assert numerator%denominator==0
        base.append(numerator//denominator)
    I=[3*(base[k] if k<len(base) else 0)+7*(base[k-1] if k else 0)
       for k in range(n)]
    D=10*M**(n-2)
    assert sum(I)==D
    assert sum(k*v for k,v in enumerate(I))==D
    facts=[factorial(k) for k in range(n+1)]
    T=[I[k]**2*facts[k]*facts[n-k] for k in range(n)]
    W=sum(T[k]*(n-1)**k for k in range(n))
    # N(p)=W/(D^2*(n-1)^n).
    special_over_N=Fraction(I[1]**2*facts[n-1]*(n-1),W)
    # For an ordinary-column deletion, scale x_1 by sqrt(z), z=9/10,
    # and divide its Fock norm by det(D_scale)^2=z.
    ordinary_numerator=sum(
        T[k]*(n-k)*(n-2)**(n-1-k)*(n-1)**(2*k)*9**k*10**(n-1-k)
        for k in range(n))
    ordinary_denominator=(n-1)**n*9*10**(n-2)*W
    ordinary_over_N=Fraction(ordinary_numerator,ordinary_denominator)
    g=Fraction(n-1,n)**(n-1)
    ratio=(special_over_N+(n-1)*ordinary_over_N)/(n*g)
    assert ratio < Fraction(99996,100000) < 1
    # The exact rational is huge; retain a reproducible digest instead of
    # printing tens of thousands of digits. The assertion above is exact.
    exact_hex=f'{ratio.numerator:x}/{ratio.denominator:x}'.encode()
    result={
        'status':'exact integer and rational assertions passed',
        'n':n,
        'special_column':['0','7/10',f'3/{10*(n-2)} repeated {n-2} times'],
        'other_columns':f'(1-u_i)/{n-1}, repeated {n-1} times',
        'trial_scale_squared':'9/10',
        'average_trial_ratio_decimal':float(ratio),
        'special_column_ratio_decimal':float(special_over_N/g),
        'ordinary_column_trial_ratio_decimal':float(ordinary_over_N/g),
        'strict_rational_upper_bound':'99996/100000',
        'exact_ratio_hex_sha256':hashlib.sha256(exact_hex).hexdigest(),
        'scope':'Refutes the averaged minimum-Fock-norm deletion comparison only; not the capacity-balanced H comparison, the max-column version, or Gyires.'}
    return result

if __name__=='__main__':
    result=certificate()
    Path('round6_average_fock_capacity_obstruction.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
