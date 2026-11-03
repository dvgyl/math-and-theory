"""Reproduce the second-edition implementation and exact-certificate audit."""
import json
from pathlib import Path

import numpy as np
import sympy as sp

from unilateral_chsh import (PAULI, bloch, canonical_optimum, unilateral_optimum,
                            normalized_chsh_squared, filter_state, effect_sqrt,
                            state_from_bloch)
from extensions_solver import (exact_activation, ellipsoid_data, shortcut,
                               success_frontier, optimal_success_original,
                               sensitivity, value_error_bound,
                               exact_shortcut_value, rank_two_value_from_bloch,
                               axial_success_frontier)


def run():
    rng=np.random.default_rng(240603945)
    errors={k:0. for k in ('shortcut','ellipsoid','raw_guard','original_success',
                           'depolarization','gradient','gradient_unrefined',
                           'frontier_witness','frontier_probability','frontier_closed_formula',
                           'exact_cubic','rank_two','axial_frontier','axial_witness',
                           'axial_probability')}
    counts={'exact_state_side_certificates':0,'guarded_shortcuts':0,
            'noise_tests':0,'gradient_directions':0,'frontier_cases':0,
            'lipschitz_pairs':0,'exact_cubic_state_sides':0,
            'irreducible_cubic_examples':0,'rank_two_state_sides':0,
            'rank_two_threshold_examples':0,'axial_frontier_cases':0,
            'rejected_out_of_scope_inputs':0}
    exact_examples=[]
    states=[]
    sig=[sp.Matrix(p) for p in (
        [[1,0],[0,1]],[[0,1],[1,0]],[[0,-sp.I],[sp.I,0]],[[1,0],[0,-1]])]
    for rank in range(1,5):
        for _ in range(6):
            X=sp.Matrix([[int(rng.integers(-4,5))+sp.I*int(rng.integers(-4,5))
                          for _ in range(rank)] for __ in range(4)])
            rho=X*X.conjugate().T
            rho=rho/sp.trace(rho)
            raw=np.array(rho.evalf(),complex)
            R=sp.Matrix(4,4,lambda i,j:sp.simplify(sp.trace(rho*sp.kronecker_product(sig[i],sig[j]))))
            a,b,T=R[1:4,0],R[0,1:4].T,R[1:4,1:4]
            for side in ('A','B'):
                cert=exact_activation(a,b,T,side)
                result=unilateral_optimum(raw,side)
                assert cert['filtered_violation']==(result['value']>1+1e-8), (rank,side,cert,result['value'])
                assert cert['initial_nonviolating']==(normalized_chsh_squared(raw)<=1+1e-8)
                if rank<=2:
                    closed=rank_two_value_from_bloch(np.array(a,float).ravel(),
                                                    np.array(b,float).ravel(),np.array(T,float),side)
                    errors['rank_two']=max(errors['rank_two'],abs(closed-result['value']))
                    counts['rank_two_state_sides']+=1
                counts['exact_state_side_certificates']+=1
                D,c=result['canonical_T'],result['canonical_c']
                states.append((D,c))
                aa,bb,TT=(np.array(a,float).ravel(),np.array(b,float).ravel(),np.array(T,float))
                if side=='B': aa,bb,TT=bb,aa,TT.T
                ce,Q=ellipsoid_data(aa,bb,TT)
                errors['ellipsoid']=max(errors['ellipsoid'],float(np.max(np.abs(Q-D.T@D))),float(np.max(np.abs(ce-c))))
                alpha=float(np.trace(D@D.T)-c@c)
                errors['raw_guard']=max(errors['raw_guard'],abs(alpha-(np.sum(TT*TT)-bb@bb)/(1-aa@aa)))
                if alpha>1+1e-8:
                    sh=shortcut(D,c)
                    errors['shortcut']=max(errors['shortcut'],abs(sh['value']-result['value']))
                    counts['guarded_shortcuts']+=1
                    u=sh['u']
                    marginal=np.eye(2)+sum(aa[i]*PAULI[i+1] for i in range(3))
                    ev,U=np.linalg.eigh(marginal)
                    W=(U*(1/np.sqrt(ev)))@U.conj().T
                    F=effect_sqrt(u)@W
                    F=F/np.linalg.norm(F,2)
                    _,p=filter_state(raw,F,side)
                    errors['original_success']=max(errors['original_success'],abs(p-optimal_success_original(aa,u)))
                    if sh['spectrum_gap'] is not None and sh['spectrum_gap']>1e-4:
                        gD,gc=sensitivity(D,c,sh['n'],sh['v'])
                        for _ in range(2):
                            dD,dc=rng.normal(size=(3,3)),rng.normal(size=3)
                            eps=1e-6
                            finite=(shortcut(D+eps*dD,c+eps*dc)['value']-
                                    shortcut(D-eps*dD,c-eps*dc)['value'])/(2*eps)
                            half=(shortcut(D+eps*dD/2,c+eps*dc/2)['value']-
                                  shortcut(D-eps*dD/2,c-eps*dc/2)['value'])/eps
                            richardson=(4*half-finite)/3
                            analytic=float(np.sum(gD*dD)+gc@dc)
                            errors['gradient_unrefined']=max(errors['gradient_unrefined'],abs(finite-analytic))
                            errors['gradient']=max(errors['gradient'],abs(richardson-analytic))
                            counts['gradient_directions']+=1
                    if counts['frontier_cases']<48 and (np.linalg.norm(u)>.01 or counts['frontier_cases']<6):
                        for p0 in (.6,.8,.95):
                            fr=success_frontier(D,c,p0)
                            errors['frontier_witness']=max(errors['frontier_witness'],abs(fr['duality_gap']))
                            errors['frontier_probability']=max(errors['frontier_probability'],max(0.,p0-fr['actual_success']))
                            counts['frontier_cases']+=1
                for visibility in (.25,.8):
                    dep=canonical_optimum(visibility*D,visibility*c)['value']
                    errors['depolarization']=max(errors['depolarization'],abs(dep-visibility**2*result['value']))
                    counts['noise_tests']+=1
    # Universal continuity certificate for physical canonical input pairs.
    largest_lipschitz_excess=-float('inf')
    for i in range(len(states)-1):
        D,c=states[i];E,e=states[i+1]
        A,B=D@D.T,E@E.T
        bound=value_error_bound(np.linalg.norm(A-B,2),abs(c@c-e@e),np.linalg.norm(D@c-E@e))
        gap=abs(canonical_optimum(D,c)['value']-canonical_optimum(E,e)['value'])
        largest_lipschitz_excess=max(largest_lipschitz_excess,float(gap-bound))
        assert gap<=bound+1e-10
        counts['lipschitz_pairs']+=1
    # Exact examples, including a rational directional activation certificate.
    rat=sp.Rational
    examples=[
        ('rank_three_activation',[0,0,0],[0,0,rat(7,20)],sp.diag(rat(7,10),-rat(7,10),rat(13,20))),
        ('alice_only_full_rank',[0,0,rat(24,25)],[0,0,rat(96,125)],sp.diag(rat(28,125),-rat(28,125),rat(4,5))),
        ('guard_counterexample',[0,0,0],[0,0,rat(3,10)],sp.diag(rat(7,20),-rat(7,20),rat(3,5))),
        ('threshold_rank_three',[0,0,0],[0,0,rat(1,4)],sp.diag(rat(1,2),-rat(1,2),rat(3,4))),
    ]
    for name,a,b,T in examples:
        for side in ('A','B'):
            cert=exact_activation(a,b,T,side)
            exact_examples.append({'name':name,'side':side,
                'guard':str(cert['raw_purity_guard']),
                'initial_nonviolating':cert['initial_nonviolating'],
                'filtered_violation':cert['filtered_violation'],
                'hidden_activation':cert['hidden_activation'],
                'activation_signs':cert.get('activation_signs'),
                'coefficients':[str(x) for x in cert.get('activation_coefficients',())]})

    # Exercise the exact root-object API on repeated roots, irrational cubic
    # roots, noncanonical input, and both filtering directions. The comparison
    # uses the universal solver, not the shortcut implemented by this API.
    cubic_cases=[
        (*examples[0], 'A', rat(79,75)),
        (*examples[0], 'B', rat(292,247)),
        (*examples[1], 'A', rat(32,25)),
        ('generic_full_rank',[0,0,0],[rat(1,10),rat(1,20),rat(1,20)],
         sp.diag(rat(7,10),-rat(3,5),rat(11,20)), 'A', None),
        ('generic_full_rank',[0,0,0],[rat(1,10),rat(1,20),rat(1,20)],
         sp.diag(rat(7,10),-rat(3,5),rat(11,20)), 'B', None),
        ('circle_of_optimizers',[0,0,0],[rat(9,20),0,0],
         sp.diag(rat(8,15),-rat(2,3),rat(3,4)), 'A', rat(145,144)),
        ('bell',[0,0,0],[0,0,0],sp.diag(1,-1,1), 'A', sp.Integer(2)),
        ('bell',[0,0,0],[0,0,0],sp.diag(1,-1,1), 'B', sp.Integer(2)),
    ]
    cubic_records=[]
    for name,a,b,T,side,expected in cubic_cases:
        raw=state_from_bloch(np.array(a,float),np.array(b,float),np.array(T,float))
        assert np.linalg.eigvalsh(raw)[0]>=-1e-12
        exact=exact_shortcut_value(a,b,T,side)
        poly=exact['scaled_eigenvalue_polynomial']
        roots=exact['scaled_eigenvalues']
        assert poly.degree()==3 and len(roots)==3
        assert all(bool(root>0) for root in roots)
        assert all(bool(roots[i]<=roots[i+1]) for i in range(2))
        if expected is not None:
            assert sp.simplify(exact['squared_value']-expected)==0
        else:
            assert poly.is_irreducible, (name,side,poly)
            counts['irreducible_cubic_examples']+=1
        value=float(sp.N(exact['squared_value'],40))
        numeric=unilateral_optimum(raw,side)['value']
        errors['exact_cubic']=max(errors['exact_cubic'],abs(value-numeric))
        counts['exact_cubic_state_sides']+=1
        cubic_records.append({'name':name,'side':side,'squared_value':str(exact['squared_value']),
                              'numerical_value':value,'polynomial':str(poly.as_expr()),
                              'distinct_roots':len(set(roots))})

    # The rank-two floor, guard equality, and strict branch are all exercised.
    singlet=np.array([0,1,-1,0],complex)/np.sqrt(2)
    for p in (rat(1,2),rat(2,3),rat(4,5),sp.Integer(1)):
        pp=float(p)
        raw=pp*np.outer(singlet,singlet.conj())+(1-pp)*np.diag([1.,0.,0.,0.])
        a,b,T=bloch(raw)
        expected=float(max(sp.Integer(1),2*p/(2-p)))
        for side in ('A','B'):
            value=rank_two_value_from_bloch(a,b,T,side)
            numeric=unilateral_optimum(raw,side)['value']
            errors['rank_two']=max(errors['rank_two'],abs(value-numeric),abs(value-expected))
            counts['rank_two_state_sides']+=1
            counts['rank_two_threshold_examples']+=int(p==rat(2,3))

    def check_axial(t,r,c0,R):
        probability=1/(1+R)
        D,c=np.diag([t,-t,r]),np.array([0.,0.,c0])
        raw=state_from_bloch(np.zeros(3),c,D)
        assert np.linalg.eigvalsh(raw)[0]>=-1e-12
        closed=axial_success_frontier(t,r,c0,probability)
        dual=success_frontier(D,c,probability)
        F=effect_sqrt(closed['u'])
        F/=np.linalg.norm(F,2)
        output,p=filter_state(raw,F)
        actual=normalized_chsh_squared(output)
        errors['axial_frontier']=max(errors['axial_frontier'],abs(closed['value']-dual['value']))
        errors['axial_witness']=max(errors['axial_witness'],abs(closed['value']-actual))
        errors['axial_probability']=max(errors['axial_probability'],max(0.,probability-p))
        counts['axial_frontier_cases']+=1
        return closed

    # Include g=0, x<r^2, x=r^2, the constant branch, and the exact branch
    # transition g^2=k(x-r^2). Positive Gram need not mean alpha>1.
    axial_families=[(.6,.7,0.),(.5,.7,.1),(.6,.6,.1),(.7,.5,.1),
                    (np.sqrt(.4),.6,.2),(.68,.63,.3)]
    modes=set()
    for t,r,c0 in axial_families:
        x,s,g=t*t,c0*c0,r*c0
        radii=[0.,.05,.2,.5,.8,1.]
        if g>0:
            radii.append(g/(x-s))
            if x>r*r and g*g>(x-s)*(x-r*r):
                radii.append((x-r*r)/g)
        for R in radii:
            modes.add(check_axial(t,r,c0,R)['mode'])
    # Independent closed expression covers the tilted and axial regimes.
    D,c=np.diag([.7,-.7,.65]),np.array([0.,0.,.35])
    for R in np.r_[0.,np.linspace(.001,.99,25),27/91,13/21,np.sqrt(27/539),1.]:
        exact=(49/50+(539/1350)*R*R if R<=27/91 else
               73/80+(91/200)*R-(147/400)*R*R if R<=13/21 else 79/75)
        fr=success_frontier(D,c,1/(1+R))
        errors['frontier_closed_formula']=max(errors['frontier_closed_formula'],abs(fr['value']-exact))
        if R>0:
            errors['frontier_witness']=max(errors['frontier_witness'],abs(fr['duality_gap']))
            errors['frontier_probability']=max(errors['frontier_probability'],max(0.,1/(1+R)-fr['actual_success']))
        else:
            assert np.array_equal(fr['u'],np.zeros(3)) and np.isinf(fr['tau'])
        closed=check_axial(.7,.65,.35,R)
        modes.add(closed['mode'])
        errors['axial_frontier']=max(errors['axial_frontier'],abs(closed['value']-exact))
        counts['frontier_cases']+=1
    assert modes=={'identity','tilted','axial','plateau'},modes

    # The public routines must reject inputs outside their stated domains;
    # in particular the rank-two floor cannot be applied to a pure marginal.
    rejected=[
        (ValueError,lambda:exact_shortcut_value(*examples[2][1:])),
        (TypeError,lambda:exact_shortcut_value([0,0,0],[0,0,0],sp.diag(.7,-.7,.7))),
        (ArithmeticError,lambda:rank_two_value_from_bloch([0,0,1],[0,0,0],np.zeros((3,3)))),
        (ValueError,lambda:axial_success_frontier(.7,.65,.35,.49)),
        (ValueError,lambda:axial_success_frontier(.7,.65,.35,1.01)),
        (ValueError,lambda:axial_success_frontier(.7,.8,.3,.8)),
        (ValueError,lambda:axial_success_frontier(.2,.3,.2,.8)),
    ]
    for exception,call in rejected:
        try:
            call()
        except exception:
            counts['rejected_out_of_scope_inputs']+=1
        else:
            raise AssertionError(f'Expected {exception.__name__} for an out-of-scope input')
    assert max(v for k,v in errors.items() if k not in ('gradient','gradient_unrefined'))<5e-8,errors
    assert errors['gradient']<5e-7,errors
    return {'status':'PASS','seed':240603945,'counts':counts,'maximum_errors':errors,
            'largest_lipschitz_excess':largest_lipschitz_excess,'exact_examples':exact_examples,
            'exact_cubic_examples':cubic_records,'axial_frontier_modes':sorted(modes),
            'scope':'Implementation checks and exact rational sign certificates; numerical checks are not proofs.'}


if __name__=='__main__':
    result=run()
    Path(__file__).with_name('extension_implementation_results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('exact_examples','exact_cubic_examples')},indent=2))
