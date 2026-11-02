#!/usr/bin/env python3
"""Exact rational GF and period-eight quasipolynomial certificate.

All identities are polynomial identities over the integers/rationals, checked
without symbolic-math dependencies. The combinatorial proof establishing the
GF is in exact_odd_enumeration.md. The independent rooted-code enumeration is
used as an additional check, never as a replacement for that proof.
"""
from pathlib import Path
from collections import Counter
from fractions import Fraction
from math import comb
import argparse,json

ROOT=Path(__file__).resolve().parent

def trim(p):
    p=list(p)
    while len(p)>1 and p[-1]==0:p.pop()
    return p
def add(*polys):
    out=[0]*max(map(len,polys))
    for p in polys:
        for i,c in enumerate(p):out[i]+=c
    return trim(out)
def scale(p,c):return trim([v*c for v in p])
def shift(p,k):return [0]*k+list(p)
def mul(a,b):
    out=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):out[i+j]+=x*y
    return trim(out)
def power(p,k):
    out=[1]
    for _ in range(k):out=mul(out,p)
    return out
def subst_power(p,k):
    out=[0]*((len(p)-1)*k+1)
    for i,c in enumerate(p):out[i*k]=c
    return trim(out)
def equal_rat(a,b):return mul(a[0],b[1])==mul(b[0],a[1])
def sum_rat(a,b):return(add(mul(a[0],b[1]),mul(b[0],a[1])),mul(a[1],b[1]))
def product_rat(a,b):return(mul(a[0],b[0]),mul(a[1],b[1]))
def sub_rat_power(a,k):return(subst_power(a[0],k),subst_power(a[1],k))
def monomial_rat(a,k,c=1):return(shift(scale(a[0],c),k),a[1])
def series(a,N):
    p,q=a;assert q[0]==1
    out=[]
    for n in range(N+1):
        out.append((p[n] if n<len(p) else 0)-sum(q[j]*out[n-j] for j in range(1,min(n,len(q)-1)+1)))
    return out

def quasipolynomial(n):
    if n==7:return 7
    assert n>=9 and n%2
    c,d={1:(-1126,2250),3:(-1090,1962),5:(-1126,2298),7:(-1090,1914)}[n%8]
    value=n**4-20*n**3+239*n*n+c*n+d
    assert value%192==0
    return value//192

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--through',type=int,default=101)
    args=parser.parse_args();data=json.loads((ROOT/'compact_odd_grammar.json').read_text())
    # Common denominator (1-x²)^3 for all ten one-leaf components.
    p=[1,0,-1];common=power(p,3)
    raw=[([0,0,1],0),([0,0,0,0,2],1),
         (shift(subst_power([1,4,-3],2),3),3),([0,0,0,1],0),
         (shift([1,0,1],3),1),(shift(subst_power([1,4,-3],2),4),3),
         ([0,0,0,0,0,2],2),([0,0,0,0,1],0),
         (shift([2,0,2],4),1),(shift([1,0,0,0,1],4),2)]
    numerators=[mul(a,power(p,3-k)) for a,k in raw]
    seeds={0:2,4:3,9:4}
    for dest in range(10):
        value=shift(common,seeds[dest]) if dest in seeds else [0]
        for rule in data['productions']:
            if rule['destination']==dest and len(rule['children'])==1:
                tag=rule['operation'];delta=1+tag[2]+tag[3]
                value=add(value,shift(numerators[rule['children'][0]],delta))
        assert numerators[dest]==value
    F=[(z,common) for z in numerators]
    A=(shift([1,0,1],2),p)
    B=([0,0,0,2],power(p,2))
    assert equal_rat(A,sum_rat(F[0],F[1]))
    assert equal_rat(B,sum_rat(sum_rat(F[3],F[4]),F[6]))
    plus=[1,0,1];plus2=[1,0,0,0,1]
    M=(shift(subst_power([1,1,2],2),4),mul(power(p,2),plus))
    assert equal_rat((scale(M[0],2),M[1]),sum_rat(product_rat(A,A),sub_rat_power(A,2)))
    terminal_terms=Counter()
    for rule in data['terminal_choices']:
        left,right=rule['left'],rule['right'];tag=rule['operation']
        if left in seeds and right<10 and tag[1]==0:
            terminal_terms[(2+seeds[left]+tag[3],right)]+=1
    enum_numerator=add(*[shift(scale(numerators[s],c),d) for (d,s),c in terminal_terms.items()])
    E=(shift(subst_power([8,4,-12,4],2),7),common)
    assert enum_numerator==E[0]
    S=(shift(subst_power([2,2,0,-2],2),7),mul(power(p,2),plus))
    # Reflection fixes either a core-edge or a core-triangle center.
    fixed_numerator=[0]
    for i in [0,1,3,4,6]:fixed_numerator=add(fixed_numerator,shift(subst_power(numerators[i],2),3))
    for i in [0,1,3,4]:fixed_numerator=add(fixed_numerator,shift(subst_power(numerators[i],2),3))
    for i in [3,4,6]:fixed_numerator=add(fixed_numerator,shift(subst_power(numerators[i],2),5))
    assert equal_rat(S,(fixed_numerator,subst_power(common,2)))
    U2=(shift(subst_power([5,6,-5,-5,3],2),7),mul(power(p,3),plus))
    U3=(shift(subst_power([2,2,4],2),9),mul(power(p,4),plus))
    U4=(shift(subst_power([1,0,4,2,6,0,3],2),11),mul(mul(power(p,5),power(plus,2)),plus2))
    assert equal_rat((scale(U2[0],2),U2[1]),sum_rat(E,S))
    assert equal_rat(U3,monomial_rat(product_rat(M,B),2))
    assert equal_rat((scale(U4[0],2),mul(U4[1], [1])),
                     product_rat(([0,0,0,1],p),sum_rat(product_rat(M,M),sub_rat_power(M,2))))
    Nt=[7,-3,-4,8,-1,4,11,-8,1,1]
    Dt=mul(mul(power([1,-1],5),power([1,1],2)),[1,0,1])
    U=(shift(subst_power(Nt,2),7),subst_power(Dt,2))
    assert equal_rat(U,sum_rat(sum_rat(sum_rat(([0]*7+[2],[1]),U2),U3),U4))

    # An exact rational identity proves the quasipolynomial for all orders.
    # For m=(n-7)/2=4k+r, use Newton's basis binomial(k,j).
    newton={0:[8,109,502,896,512],1:[18,177,678,1024,512],
            2:[36,280,886,1152,512],3:[66,420,1126,1280,512]}
    d4=power([1,0,0,0,-1],5);qn=scale(d4,-1)  # correction at n=7
    for r,coeffs in newton.items():
        for j,c in enumerate(coeffs):qn=add(qn,shift(scale(power([1,0,0,0,-1],4-j),c),r+4*j))
    assert mul(qn,Dt)==mul(Nt,d4)
    for r,coeffs in newton.items():
        for k in range(1 if r==0 else 0,6):
            n=8*k+2*r+7
            assert sum(c*comb(k,j) for j,c in enumerate(coeffs) if j<=k)==quasipolynomial(n)
    values=series(U,args.through);parts=[series(z,args.through) for z in [U2,U3,U4]]
    rows=[]
    for n in range(7,args.through+1,2):
        assert values[n]==quasipolynomial(n)
        rows.append(dict(n=n,total=values[n],path_core=parts[0][n],one_branch=parts[1][n],two_branches=parts[2][n],complete_core=2 if n==7 else 0))
    census=json.loads((ROOT/'odd_grammar_enumeration.json').read_text())
    for state,counts in census['one_leaf_component_counts'].items():
        assert counts==series(F[int(state)],len(counts)-1)
    e_coeff=series(E,args.through);s_coeff=series(S,args.through)
    for row in census['rows']:
        n=row['n']
        if n>args.through:continue
        expected={str(k):parts[k-2][n] for k in range(2,5) if parts[k-2][n]}
        if n==7:expected['1']=2
        assert row['by_core_leaves']==expected and row['extremizers']==values[n]
        assert row['path_end_rooted_classes']==e_coeff[n]
        assert row['path_end_exchange_symmetric_classes']==s_coeff[n]
    report=dict(passed=True,gf_numerator_in_t=Nt,
                gf_denominator_factors='(1-t)^5(1+t)^2(1+t^2)',t='x^2',prefactor='x^7',
                quasipolynomial_denominator=192,quasipolynomial_threshold=9,
                common_high_terms='n^4-20n^3+239n^2',
                residue_linear_constant={str(r):[c,d] for r,(c,d) in {1:(-1126,2250),3:(-1090,1962),5:(-1126,2298),7:(-1090,1914)}.items()},
                initial_exception={'n':7,'count':7},
                all_component_recurrences_checked=True,all_rational_identities_checked=True,
                quasipolynomial_certified_by_integer_polynomial_identity=True,
                exact_grammar_enumeration_match_through=min(args.through,census['maximum_order']),
                independently_enumerated_components_and_end_symmetries_match=True,
                leading_asymptotic='a_n ~ n^4/192 through odd n',rows=rows)
    (ROOT/'exact_odd_count_verification.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k!='rows'},indent=2))
    print('counts:',[(r['n'],r['total']) for r in rows[:15]])

if __name__=='__main__':main()
