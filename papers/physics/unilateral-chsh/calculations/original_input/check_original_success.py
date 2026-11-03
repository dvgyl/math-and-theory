"""Reproduce direct-matrix, polynomial, lens and closed-frontier checks."""
import json
from pathlib import Path

import numpy as np
import sympy as sp

from original_success import *


def bloch(rho):
    a=np.array([np.trace(rho@np.kron(s,I2)).real for s in PAULI])
    b=np.array([np.trace(rho@np.kron(I2,s)).real for s in PAULI])
    D=np.array([[np.trace(rho@np.kron(s,t)).real for t in PAULI] for s in PAULI])
    return a,b,D


def direct_score(rho,F):
    FF=np.kron(F,I2)
    out=FF@rho@FF.conj().T
    prob=np.trace(out).real
    T=bloch(out/prob)[2]
    sv=np.linalg.svd(T,compute_uv=False)
    return float(sv[0]**2+sv[1]**2),float(prob)


def random_canonical(rng,rank):
    X=rng.normal(size=(4,rank))+1j*rng.normal(size=(4,rank))
    rho=X@X.conj().T;rho/=np.trace(rho)
    ra=np.trace(rho.reshape(2,2,2,2),axis1=1,axis2=3)
    ev,V=np.linalg.eigh(2*ra)
    W=(V*(1/np.sqrt(ev)))@V.conj().T
    WW=np.kron(W,I2);out=WW@rho@WW.conj().T
    return bloch(out)[1:]


def main():
    rng=np.random.default_rng(861703039)
    residuals={}
    records=[]

    def record(key,value):
        residuals[key]=max(residuals.get(key,0.0),float(abs(value)))

    # These direct computations do not use the 3x3 Gram formula.
    for i in range(180):
        c,D=random_canonical(rng,2+i%3)
        a=rng.normal(size=3);a*=rng.uniform(0,.94)/np.linalg.norm(a)
        u=rng.normal(size=3);u*=rng.uniform(0,.99)/np.linalg.norm(u)
        raw=original_density(c,D,a)
        ev,V=np.linalg.eigh(I2+np.einsum("i,ijk->jk",a,PAULI))
        W=(V*(1/np.sqrt(ev)))@V.conj().T
        F=sqrt_psd(I2+np.einsum("i,ijk->jk",u,PAULI))@W
        pmax=1/np.linalg.eigvalsh(F.conj().T@F)[-1]
        score,prob=direct_score(raw,np.sqrt(pmax)*F)
        record("direct_gram_score",score-score_squared(c,D,u))
        record("success_formula",prob-maximum_success(a,u))
        p0=rng.uniform(0,1)
        assert (pmax>=p0)==(lens_slacks(a,u,p0)[1]>=0)
        # Raw orientation-free ellipsoid identity in the nonsingular cases.
        if abs(np.linalg.det(D))>1e-9:
            Q=D.T@D;Qi=np.linalg.inv(Q);g=D.T@a;w=D.T@u
            G=(1-w@Qi@w)*(Q-np.outer(c,c))+np.outer(c+w,c+w)
            record("ellipsoid_gram",np.linalg.norm(G-bob_gram(c,D,u)))
            record("ellipsoid_lens",np.linalg.norm(a-p0*u)**2
                   -(g-p0*w)@Qi@(g-p0*w))

    def compare_family(name,c,D,a,p0,expected,explicit_u):
        rho=original_density(c,D,a)
        actual=score_squared(c,D,explicit_u)
        record(name+"_explicit",actual-expected)
        result=numerical_frontier(c,D,a,p0,starts=12,
                                  seed=int(rng.integers(0,2**31)))
        gap=result["score_squared"]-expected
        if abs(gap)>2e-7:
            result=numerical_frontier(c,D,a,p0,starts=40,
                                      seed=int(rng.integers(0,2**31)))
            gap=result["score_squared"]-expected
        record(name+"_numerical",gap)
        assert abs(gap)<2e-6,(name,p0,expected,result)
        assert min(result["feasibility_slacks"])>-1e-8
        if name!="product":
            score,prob=direct_score(rho,concentration_filter(a,p0))
            record(name+"_original_filter",score-expected)
            assert prob>=p0-1e-10
        records.append({"family":name,"p0":p0,"a_norm":float(np.linalg.norm(a)),
                        "expected":expected,"numerical":result["score_squared"],
                        "gap":gap,"effect":result["effect"]})

    for t in [.3,.65,.8,1.]:
        for r in [.2,.6,.96]:
            a=rng.normal(size=3);a*=r/np.linalg.norm(a)
            R,_=np.linalg.qr(rng.normal(size=(3,3)))
            if np.linalg.det(R)<0:R[:,0]*=-1
            D=t*R@np.diag([1,-1,1])
            for p0 in [.01,.05,.2,.5,.85,1.]:
                compare_family("conformal",np.zeros(3),D,a,p0,
                    conformal_frontier(t,r,p0),minimum_norm_effect(a,p0))

    for population in [.15,.5,.85]:
        for t in [.3,.8,1.]:
            a=np.array([0.,0.,2*population-1])
            D=np.diag([t,-t,1.])
            for p0 in [.05,.3,.7,1.]:
                expected=correlated_frontier(population,
                    t*np.sqrt(population*(1-population)),p0)
                compare_family("correlated",np.zeros(3),D,a,p0,expected,
                               minimum_norm_effect(a,p0))

    for r in [0.,.3,.8]:
        for bn in [0.,.4,1.]:
            a=np.array([0.,0.,r]);c=np.array([bn,0.,0.])
            for p0 in [.05,.4,.8,1.]:
                _,rmax=radius_range(r,p0)
                u=np.array([0.,0.,rmax])
                compare_family("product",c,np.zeros((3,3)),a,p0,
                               product_frontier(r,bn,p0),u)

    # Singular ellipsoid reduction: align only the invisible null component.
    singular_cases=0
    for rank in [0,1,2]:
        diag=np.array([.2,-.15,.1]);diag[rank:]=0
        D=np.diag(diag);Q=D.T@D;Qi=np.linalg.pinv(Q)
        c=np.array([.04,.06,.08])
        for null_a in [False,True]:
            for j in range(16):
                a=rng.normal(size=3)
                if not null_a:a[rank:]=0
                if np.linalg.norm(a):a*=.6/np.linalg.norm(a)
                u=rng.normal(size=3);u*=rng.uniform(0,.95)/np.linalg.norm(u)
                w=D.T@u;g=D.T@a
                apar=D@Qi@g;anull=a-apar
                upar=D@Qi@w;unull=u-upar
                eta=anull@anull
                if eta>1e-14:
                    k=np.sqrt(eta)*np.linalg.norm(unull)
                    aligned=upar+(k/eta)*anull
                    q=w@Qi@w+k*k/eta
                else:
                    aligned=u.copy()
                    q=w@Qi@w+unull@unull
                p0=.7*maximum_success(a,u)
                assert maximum_success(a,aligned)>=maximum_success(a,u)-1e-10
                G=(1-q)*(Q-np.outer(c,c))+np.outer(c+w,c+w)
                record("singular_gram",np.linalg.norm(G-bob_gram(c,D,u)))
                record("singular_aligned_score",
                       score_squared(c,D,u)-score_squared(c,D,aligned))
                singular_cases+=1

    # Exact symbolic checks of the rational pseudoinverse and all rank strata.
    Rat=sp.Rational
    rotation=sp.Matrix([[Rat(3,5),-Rat(4,5),0],
                        [Rat(4,5),Rat(3,5),0],[0,0,1]])
    symbolic_strata=0
    for rank in [0,1,2,3]:
        entries=[Rat(1,5),-Rat(3,20),Rat(1,10)]
        entries[rank:]=[0]*(3-rank)
        D=sp.diag(*entries)*rotation
        Q=D.T*D;Qi=exact_psd_pseudoinverse(Q)
        assert sp.simplify(Q*Qi*Q-Q)==sp.zeros(3)
        assert sp.simplify(Qi-Q.pinv())==sp.zeros(3)
        for null_a in [False,True]:
            av=sp.Matrix([Rat(1,5),Rat(1,10),Rat(3,10)])
            if not null_a:
                av=D*Qi*D.T*av
            c=sp.Matrix([Rat(1,25),Rat(3,50),Rat(2,25)])
            b=c+D.T*av
            problem=symbolic_ellipsoid_problem(Q,c,b,(av.T*av)[0],Rat(3,4))
            assert len(problem["variables"])<=3
            assert not any(v.has(sp.sqrt(2)) for v in problem["feasibility_polynomials"])
            for v in problem["feasibility_polynomials"]+problem["psd_coefficients"]:
                poly=sp.Poly(v,*problem["variables"])
                assert all(x.is_Rational for x in poly.all_coeffs()) if len(problem["variables"])==1 else all(x.is_Rational for x in poly.coeffs())
            symbolic_strata+=1

    # The shifted-reduction counterexample is rational and full rank.
    rho=sp.Matrix([[116,0,0,56],[0,44,8,0],[0,8,11,0],[56,0,0,29]])/200
    assert 116*29-56**2==228
    assert 44*11-8**2==420
    c=sp.zeros(3,1);D=sp.diag(Rat(4,5),-Rat(3,5),Rat(9,20))
    a=sp.Matrix([0,0,Rat(3,5)])
    problem=symbolic_problem(c,D,a,1)
    at_identity=problem["gram"].subs(dict(zip(problem["variables"],a)))
    eigenvalues=sorted(at_identity.eigenvals())
    actual=sp.simplify(sum(eigenvalues[-2:]))
    false_reduced=Rat(16,25)**2+Rat(9,20)**2
    assert actual==Rat(16,25)
    assert false_reduced==Rat(6121,10000)

    # rho2 threshold and the physically normalized filter are exact.
    p=sp.symbols("p",positive=True)
    pcrit=4*(4+sp.sqrt(7))/225
    score=Rat(16,25)*(2-(1-1/(25*p))**2)
    assert sp.simplify(score.subs(p,pcrit)-1)==0
    assert sp.simplify(score.subs(p,1)-Rat(10784,15625))==0
    assert sp.simplify(score.subs(p,Rat(1,25))-Rat(32,25))==0
    fplus=(50*p-1)/49
    assert sp.simplify(Rat(49,50)*fplus+Rat(1,50)-p)==0

    report={"seed":861703039,"random_direct_matrix_checks":180,
            "closed_frontier_comparisons":len(records),
            "singular_alignment_cases":singular_cases,
            "exact_rational_rank_strata":symbolic_strata,
            "maximum_residuals":residuals,
            "rho2_threshold_exact":str(pcrit),
            "rho2_threshold_decimal":float(pcrit),
            "counterexample_true":str(actual),"counterexample_false_reduced":str(false_reduced),
            "frontier_records":records}
    Path(__file__).with_name("original_success_results.json").write_text(json.dumps(report,indent=2))
    print(json.dumps({k:v for k,v in report.items() if k!="frontier_records"},indent=2))


if __name__=="__main__":
    main()
