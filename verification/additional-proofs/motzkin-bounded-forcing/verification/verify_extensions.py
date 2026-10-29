#!/usr/bin/env python3
"""Exact certificates for the calculus-free proof and its extensions.

No floats, third-party packages, assert statements, or network access are used.
Successful execution checks algebraic identities and finite certificates. It is
NOT a Lean run and is NOT a stand-alone formalization of induction over all n.
The universal reasoning and sign hypotheses are in the written proof.
"""
from __future__ import annotations
import argparse
from fractions import Fraction as F
import json
from pathlib import Path
from exact_poly import Poly

class CertificateFailure(ArithmeticError):
    pass


def sequence_values(last: int) -> tuple[list[int], list[int]]:
    M = [1, 1]
    for n in range(1, last):
        u = (2*n+3)*M[n]+3*n*M[n-1]
        if u % (n+3):
            raise CertificateFailure('Motzkin recurrence is not integral')
        M.append(u//(n+3))
    T = [1]
    for m in M[1:]:
        T.append(m-T[-1])
    return M, T


def verify(path: Path, regressions: bool = True) -> dict:
    data = json.loads(path.read_text())
    checks: list[str] = []

    def require(name: str, condition: bool) -> None:
        if not condition:
            raise CertificateFailure(name)
        checks.append(name)

    def shifted_positive(p: Poly, start: int) -> bool:
        x = Poly.variable(1, 0)
        c = p.evaluate([x+start]).coefficients()
        return c[0] > 0 and all(v >= 0 for v in c)

    require('schema version', data['schema_version'] == 1)
    require('coefficient order', data['coefficient_order'] == 'increasing degree')
    require('forcing bound is two', data['forcing_bound'] == 2)
    require('universal seed index', data['uniform_start_index'] == 12)
    require('quantitative constant', data['quantitative_constant'] == 800)
    n = Poly.variable(1, 0)
    P = Poly.from_coefficients(data['P'])
    m = n+3
    D = 16*m**3
    V = 48*m**3-72*m**2+9*m+32
    Y = (n+2)*(2*V+3*D)-4*m
    Z = m*(2*Y+3*V*(n+4))+4*m*(n+4)
    require('universal polynomial identity for the corner value',
            (n+5)*D*Y**3-(n+4)**2*V**3*Z == m*P)
    require('all coefficients of P are positive', all(c > 0 for c in data['P']))
    require('P has degree twelve', len(data['P']) == 13)

    W = 48*(n+3)**2-72*(n+3)+9
    Vprev = 48*(n+2)**3-72*(n+2)**2+9*(n+2)+32
    Hprev = 16*n**2+40*n+19
    lowraw = 32*(n+1)*(n+3)**2*Vprev + 768*(n+1)*(n+3)**2*(n+2)**3 \
             - 4*Vprev - (n+3)*W*Vprev
    upraw = V*Hprev - 32*(n+1)*(n+3)**2*Hprev \
            - 256*(n+1)*(n+3)**2*(n+2)**2 - 4*Hprev
    lower = Poly.from_coefficients(data['envelope_lower_numerator'])
    upper = Poly.from_coefficients(data['envelope_upper_numerator'])
    require('lower-envelope cleared identity', lowraw == lower)
    require('upper-envelope cleared identity', upraw == upper)
    require('lower-envelope numerator positive for n >= 13', shifted_positive(lower, 13))
    require('upper-envelope numerator positive for n >= 13', shifted_positive(upper, 13))
    require('lower-envelope denominator polynomial positive', shifted_positive(Vprev, 13))
    require('upper-envelope denominator polynomial positive', shifted_positive(Hprev, 13))

    quantitative = P - 800*65536*(n+3)**8*(n+4)**3*(n+5)
    require('quantitative-gap shifted coefficient identity',
            quantitative.evaluate([n+12]).coefficients() == data['quantitative_shift_at_12'])
    require('quantitative-gap shifted coefficients positive',
            all(v > 0 for v in data['quantitative_shift_at_12']))
    require('lower range numerator', shifted_positive(16*n**2-120*n-477, 12))
    require('upper range numerator', shifted_positive(72*n**2+423*n+589, 12))
    require('size induction identity', 2*(n+2)**2-(n+3)**2 == n**2+2*n-1)
    require('size induction sign', shifted_positive(n**2+2*n-1, 13))
    require('local lower y margin', shifted_positive(200*n-1703, 12))
    require('local upper y margin', F(18)-F(1,50) == F(899,50) > 0)
    require('local lower z margin', shifted_positive(150*n-1451, 12))
    require('slope beta cleared identity',
            (n+3)*(7*n+20)-5*(n+4)*(n+5) == 2*n**2-4*n-40)
    require('slope beta sign', shifted_positive(2*n**2-4*n-40, 12))
    require('fixed error rectangle contains seed error bound', F(1,1800) < F(1,100))

    # Universal factorization for changes in r, with no derivatives.
    r, s, y, z, alpha, beta = [Poly.variable(6, i) for i in range(6)]
    ys = y+alpha*(s-r)
    zs = z+beta*(s-r)
    require('r difference factorization',
        ys**3-s**3*zs-(y**3-r**3*z) ==
        (s-r)*(alpha*(ys**2+ys*y+y**2)-(s**2+s*r+r**2)*z-s**3*beta))
    r, y, z, gamma, delta, t = [Poly.variable(6, i) for i in range(6)]
    yt, zt = y+gamma*t, z+delta*t
    require('u difference factorization',
        yt**3-r**3*zt-(y**3-r**3*z) ==
        t*(gamma*(yt**2+yt*y+y**2)-r**3*delta))
    require('v difference factorization',
        y**3-r**3*(z+delta*t)-(y**3-r**3*z) == -r**3*delta*t)

    # An explicit nonnegative decomposition for the bound on the r factor.
    r,s,y1,y2,alpha,z,beta = [Poly.variable(7,i) for i in range(7)]
    a = F(8,3)
    S = y1**2+y1*y2+y2**2
    R = r**2+r*s+s**2
    B = alpha*S-z*R-beta*s**3
    rhs = (2-alpha)*S+2*(243-S)+(z-19)*R+19*(R-3*a*a) \
          +(beta-5)*s**3+5*(s**3-a**3)
    require('r-factor margin decomposition', -B-F(382,27) == rhs)
    require('upper y product deficit decomposition',
        243-S == (9-y1)*(9+y1)+(9-y2)*(9+y2)+(9-y1)*y2+9*(9-y2))
    require('lower r product surplus decomposition',
        R-3*a*a == (r-a)*(r+a)+(s-a)*(s+a)+(s-a)*r+a*(r-a))
    require('cubic order factorization', s**3-a**3 == (s-a)*(s**2+s*a+a*a))
    require('exact negative margin', F(486)-3*a*a*19-a**3*5 == -F(382,27))

    r,y1,y2,eta = [Poly.variable(4,i) for i in range(4)]
    S = y1**2+y1*y2+y2**2
    require('u-factor positive margin decomposition',
        S-eta*r**3-93 == (S-147)+(2-eta)*r**3+2*(27-r**3))
    require('lower y product surplus decomposition',
        S-147 == (y1-7)*(y1+7)+(y2-7)*(y2+7)+(y1-7)*y2+7*(y2-7))
    require('upper cubic deficit decomposition', 27-r**3 == (3-r)*(9+3*r+r**2))

    # Algebraic replacement for the logarithmic transfer: equality of all four
    # Laurent-monomial exponent polynomials, for H_(n+1)=H_n*C_n^(n(n+1)).
    old = [-n*(n+1), 2*(n*n-1), -n*(n-1), Poly.constant(1,0)]
    new = [Poly.constant(1,0), -(n+1)*(n+2), 2*((n+1)**2-1), -n*(n+1)]
    for j, k in enumerate([1,-3,3,-1]):
        require(f'multiplicative transfer exponent {j}', new[j] == old[j]+k*n*(n+1))

    # Finite data are regenerated from the original Motzkin recurrence.
    M,T = sequence_values(150 if regressions else 20)
    require('initial T values', T[:16] == data['T_0_through_15'])
    for k in range(2, len(T)):
        if (k+2)*T[k] != k*(2*T[k-1]+3*T[k-2])+2*(-1)**k:
            raise CertificateFailure('recurrence regression')
    checks.append('recurrence regression, separate from universal recurrence proof')
    x = Poly.variable(1,0)
    A = lambda k: T[k]+(x-1)*(-1)**k
    require('family seed minimum exceeds lower envelope', F(30536,11299)>F(1081,400))
    require('family seed maximum below upper envelope', F(30537,11298)<F(145967,54000))
    require('family seed size', 11298>8*15**2)
    s,t = [Poly.variable(2,i) for i in range(2)]
    require('family seed monotonicity cross-product',
        (30537-s)*(11298+t)-(30537-t)*(11298+s) == 41835*(t-s))

    for k in range(2,12):
        p = A(k)*A(k+2)**3-A(k+1)**3*A(k+3)
        saved = data['family_ratio_polynomials'][str(k)]
        require(f'family cubic Q_{k}', p.coefficients() == saved and len(saved) == 4)
        c0,c1,c2,c3 = saved
        if k%2 == 0:
            require(f'Q_{k} strictly increasing on [0,1]', c3>0 and c2<0 and c1+2*c2>0)
        else:
            require(f'Q_{k} strictly decreasing on [0,1]', c3<0 and c1+2*max(c2,0)<0)

    Q = lambda k,s: (T[k]+(s-1)*(-1)**k)*(T[k+2]+(s-1)*(-1)**(k+2))**3 \
        -(T[k+1]+(s-1)*(-1)**(k+1))**3*(T[k+3]+(s-1)*(-1)**(k+3))
    for k,end in [(8,F(0)),(10,F(0)),(11,F(1))]:
        require(f'positive uniform minimum of Q_{k}', Q(k,end)>0)
    require('original ratio obstruction', Q(9,F(1)) == -92071225688)
    require('Q_2 negative below 6/25', Q(2,F(6,25))<0)
    require('Q_3 positive below 6/25', Q(3,F(6,25))>0)

    def rootgap(k: int, s: F) -> F:
        aa = lambda j: F(T[j])+(s-1)*(-1)**j
        return aa(k)**(k*k-1)-aa(k-1)**(k*(k+1)//2)*aa(k+1)**(k*(k-1)//2)

    root_bases = {}
    for k in range(6,12):
        worst = F(k%2)  # even: s=0; odd: s=1
        v = rootgap(k,worst)
        require(f'uniform root base at n={k}', v>0)
        root_bases[str(k)] = {'worst_parameter':int(worst),
                             'gap_positive':True,
                             'gap_numerator_bits':v.numerator.bit_length()}
    require('original root obstruction', rootgap(5,F(1))<0)
    require('root-gap-two factorization',
        (1+x)**3-(1-x)**3*(3-x) == -(x*x-6*x+1)*(x*x-x+2))

    den = data['isolating_denominator']
    require('isolating denominator', den == 1000000)
    def brackets(kind: str, func, order: list[int]):
        items = data[kind]
        intervals = {}
        for key,pair in items.items():
            k = int(key)
            lo,hi = (F(v,den) for v in pair)
            require(f'{kind}: interval lies inside [0,1] for {k}', 0<lo<hi<1)
            vl,vh = func(k,lo),func(k,hi)
            correct = vl<0<vh if k%2==0 else vl>0>vh
            require(f'{kind}: exact isolating signs for {k}', correct)
            intervals[k] = (lo,hi)
        for i,j in zip(order,order[1:]):
            require(f'{kind}: root order {i} before {j}', intervals[i][1]<intervals[j][0])
        return intervals
    require('ratio root order specification',data['ratio_root_order']==[6,4,5,7,9])
    require('root-gap root order specification',data['root_gap_root_order']==[4,2,3,5])
    qi=brackets('ratio_root_brackets',Q,[6,4,5,7,9])
    ri=brackets('root_gap_root_brackets',rootgap,[4,2,3,5])
    require('rho_5 below the auxiliary cutoff', qi[5][1]<F(6,25))
    for key,expected in [('original_sharp_ratio_tail',10),('original_sharp_root_tail',5),
                         ('family_uniform_sharp_ratio_tail',10),('family_uniform_sharp_root_tail',5)]:
        require(key,data[key]==expected)

    regression = {'performed':regressions,'purpose':'diagnostic only; not an infinite proof'}
    if regressions:
        count_q=count_r=0
        for j in range(17):
            s=F(j,16)
            for k in range(10,121):
                if not Q(k,s)>0:
                    raise CertificateFailure('family ratio regression')
                count_q+=1
            for k in range(6,31):
                if not rootgap(k,s)>0:
                    raise CertificateFailure('family root regression')
                count_r+=1
        regression.update({'rational_parameters':17,'ratio_checks':count_q,'root_checks':count_r})

    return {'status':'passed','lean_verified':False,
        'proof_assistant_run':False,'floating_point_used':False,
        'exact_check_count':len(checks),'checks':checks,
        'uniform_root_bases':root_bases,'regressions':regression,
        'scope':'Exact algebraic and finite certificates; universal implications are supplied by the written proof.'}


def main() -> None:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--certificates',type=Path,default=Path(__file__).resolve().parents[1]/'proof/certificates.json')
    parser.add_argument('--output',type=Path)
    parser.add_argument('--no-regressions',action='store_true')
    args=parser.parse_args()
    report=verify(args.certificates,not args.no_regressions)
    text=json.dumps(report,indent=2)+'\n'
    if args.output:
        args.output.write_text(text)
    else:
        print(text,end='')

if __name__=='__main__':
    main()
