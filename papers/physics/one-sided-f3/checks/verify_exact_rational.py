#!/usr/bin/env python3
"""Reproducible exact-arithmetic certificates for exact_rational.py.

All acceptance assertions use rational/polynomial arithmetic. A final,
separately labeled Float64 comparison is only an additional smoke check.
"""
from pathlib import Path
import json
import sympy as sp
from exact_rational import (Z,Y,I2,PAULI,one_sided_exact,both_sides_exact,
                            validate_rational_bloch)

R=sp.Rational


def exact_bloch(rho):
    a=sp.Matrix([sp.trace(rho*sp.kronecker_product(s,I2)) for s in PAULI])
    b=sp.Matrix([sp.trace(rho*sp.kronecker_product(I2,s)) for s in PAULI])
    T=sp.Matrix(3,3,lambda i,j:sp.trace(rho*sp.kronecker_product(PAULI[i],PAULI[j])))
    return a,b,T


def check_result(result,expected=None,expected_order=None):
    assert len(result.state.principal_minors)==15
    assert all(value>=0 for _,value in result.state.principal_minors)
    if expected is not None:
        assert result.certifies_rational_value(expected),(result.value_squared,expected)
    if expected_order is not None:
        assert result.derivative_order==expected_order
    if result.Q is not None:
        Q,c=result.Q,result.c
        A=Z*sp.eye(3)-Q
        assert sp.Poly(A.det()-result.D.as_expr(),Z,domain=sp.QQ).is_zero
        direct_N=(c.T*Q*A.adjugate()*c)[0]
        assert sp.Poly(direct_N-result.N.as_expr(),Z,domain=sp.QQ).is_zero
        direct_P=(A*A-Q*c*c.T).det()
        assert sp.Poly(direct_P-result.P.as_expr(),Z,domain=sp.QQ).is_zero
        assert result.P.rem(result.nu_minpoly).is_zero
        r=result.derivative_order
        D,N=result.D,result.N
        for _ in range(r):
            assert D.rem(result.eta_minpoly).is_zero
            assert N.rem(result.eta_minpoly).is_zero
            D,N=D.diff(),N.diff()
        assert not D.rem(result.eta_minpoly).is_zero
        identity=sp.Poly(Z+result.invariants['beta'],Z,domain=sp.QQ)*D+N-result.value_residue*D
        assert identity.rem(result.eta_minpoly).is_zero
    minimal=result.value_minimal_polynomial()
    assert result.certifies_value_polynomial(minimal.as_expr())
    if expected is not None:
        assert minimal==sp.Poly(Y-expected,Y,domain=sp.QQ)
    return minimal


def main():
    cases=[];evaluated=[]
    def add(name,a,b,T,side='A',expected=None,order=None):
        result=one_sided_exact(a,b,T,side)
        minimal=check_result(result,expected,order)
        entry={'name':name,'expected_rational_value':None if expected is None else str(expected),
               **result.to_dict(include_principal_minors=True)}
        entry['squared_value_minimal_polynomial']=str(minimal.as_expr())
        cases.append(entry);evaluated.append(result)
        return result
    for p in [R(0),R(1,4),R(1,2),R(1)]:
        for side in ['A','B']:
            add(f'Werner_p_{p}_{side}',[0,0,0],[0,0,0],-p*sp.eye(3),side,3*p*p,
                3 if p==0 else 0)
    product=add('product_Q_zero_triple_pole',[0,0,0],[0,0,R(3,5)],sp.zeros(3),
                expected=R(9,25),order=3)
    assert not product.attained_invertibly
    add('product_opposite_direction',[0,0,0],[0,0,R(3,5)],sp.zeros(3),'B',R(0),3)
    flat=add('rank_one_flat',[0,0,0],[0,0,0],sp.diag(0,0,R(1,2)),
             expected=R(1,4),order=1)
    assert flat.attained_invertibly
    add('rank_two_double_pole_flat',[0,0,0],[0,0,R(1,5)],sp.diag(R(1,5),-R(1,5),0),
        expected=R(2,25),order=2)
    hard=add('nonzero_gradient_hard_case',[0,0,0],[0,0,R(3,10)],
             sp.diag(R(1,5),R(1,10),R(1,50)),expected=R(36,275),order=1)
    assert not hard.attained_invertibly
    violating=add('rational_violating_state',[0,0,0],[0,0,R(1,8)],
                  sp.diag(R(3,4),-R(3,4),R(3,4)),expected=R(963,568),order=0)
    assert violating.attained_invertibly
    a=sp.Matrix([0,0,1]);b=sp.Matrix([R(1,5),R(3,10),R(1,10)])
    pure=add('pure_filtered_marginal',a,b,a*b.T,expected=R(7,50))
    assert pure.branch=='pure_filtered_marginal' and pure.attained_invertibly
    add('pure_opposite_marginal',a,b,a*b.T,'B',R(1))
    for side in ['A','B']:
        add(f'pure_entangled_{side}',[0,0,R(7,25)],[0,0,R(7,25)],
            sp.diag(R(24,25),-R(24,25),1),side,R(3),0)
    noncanonical=add('rational_original_coordinates',[-R(15,17),0,0],[-R(14,85),0,0],
        sp.diag(R(18,85),R(2,85),R(4,425)),expected=R(4,25),order=0)
    assert noncanonical.c==sp.Matrix([R(1,10),0,0])
    assert noncanonical.Q==sp.diag(R(9,100),R(1,400),R(1,2500))

    c=sp.Matrix([R(1,5),R(1,6),R(1,7)])
    S=sp.diag(R(1,20),R(1,15),R(1,10))
    galois=add('physical_Galois_state',[0,0,0],c,S,order=0)
    assert isinstance(galois.nu,sp.CRootOf)
    assert galois.nu_minpoly.degree()==6 and galois.value_minimal_polynomial().degree()==6
    primitive=sp.Poly(3175200000000000*Z**6-107604000000000*Z**5+
        65685000000*Z**4+18599100000*Z**3-188411500*Z**2+695840*Z-913,Z)
    assert galois.P.monic()==primitive.monic()
    assert galois.value_residue.degree()>0
    rotation=sp.Matrix([[R(3,5),-R(4,5),0],[R(4,5),R(3,5),0],[0,0,1]])
    rotated=add('Galois_state_rational_Bob_rotation',[0,0,0],rotation*c,S*rotation.T,order=0)
    assert rotated.P==galois.P and rotated.value_residue==galois.value_residue

    X=sp.Matrix([[1,2,0,1],[0,2,1,0],[1,0,3,1],[0,1,1,2]])
    rho=X*X.T;rho/=sp.trace(rho)
    a,b,T=exact_bloch(rho)
    pair=both_sides_exact(a,b,T)
    for side,result in pair.items():
        minimal=check_result(result)
        cases.append({'name':f'generic_rational_density_{side}',**result.to_dict(),
            'squared_value_minimal_polynomial':str(minimal.as_expr())})
        evaluated.append(result)
    assert pair['A'].state is pair['B'].state

    rejected=[]
    for name,a,b,T,error in [
        ('nonphysical_principal_minor',[0,0,0],[0,0,0],2*sp.eye(3),ValueError),
        ('floating_input',[0.,0,0],[0,0,0],sp.zeros(3),TypeError),
        ('irrational_input',[0,0,0],[0,0,sp.sqrt(2)/10],sp.zeros(3),TypeError),
    ]:
        try:
            validate_rational_bloch(a,b,T)
        except error as exc:
            rejected.append({'name':name,'exception':type(exc).__name__,'message':str(exc)})
        else:
            raise AssertionError(f'{name} was incorrectly accepted.')

    # ONLY this final optional layer converts the exact results to decimals.
    # No exact assertion above depends on the following comparison.
    import numpy as np
    from f3_exact import one_sided
    maximum_gap=0.
    for result in evaluated:
        a=np.array(result.state.a,dtype=float).reshape(3)
        b=np.array(result.state.b,dtype=float).reshape(3)
        T=np.array(result.state.T,dtype=float)
        approximate=one_sided(a,b,T,result.side)['F3_squared']
        exact_as_decimal=float(sp.N(result.value_squared,40))
        maximum_gap=max(maximum_gap,abs(approximate-exact_as_decimal))
    output={'sympy_version':sp.__version__,'exact_cases':len(cases),
        'principal_minors_per_validated_state':15,
        'pole_orders_exercised':sorted({r.derivative_order for r in evaluated if r.derivative_order is not None}),
        'all_exact_checks_passed':True,'rejected_invalid_inputs':rejected,
        'additional_decimal_comparison':{'not_used_for_exact_certification':True,
            'maximum_absolute_difference_from_float64_evaluator':maximum_gap},
        'cases':cases,
        'scope':'Exact QQ/CRootOf evaluation for rational input; all arbitrary-real theorems remain mathematical statements. No new Lean claim.'}
    Path(__file__).with_name('exact_rational_results.json').write_text(json.dumps(output,indent=2)+'\n')
    print(json.dumps({key:value for key,value in output.items() if key!='cases'},indent=2))


if __name__=='__main__':
    main()
