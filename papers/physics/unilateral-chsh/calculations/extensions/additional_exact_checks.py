"""Independent checks for the later rational-cubic and tilted-frontier results."""
import json
from pathlib import Path

import numpy as np
import sympy as sp

if __package__:
    from .independent_checks import (I3, canonical, data, direct_filtered, direct_max,
                                     random_state, shortcut)
else:
    from independent_checks import (I3, canonical, data, direct_filtered, direct_max,
                                    random_state, shortcut)


def main():
    rng = np.random.default_rng(861704203)
    residuals = {}
    count = 0

    def record(key, value):
        residuals[key] = max(residuals.get(key, 0.0), float(abs(value)))

    for rank in [2, 3, 4]:
        for _ in range(180):
            rho, _ = canonical(random_state(rng, rank))
            c, D, A, s, d, C, K = data(rho)
            alpha = np.trace(A)-s
            if alpha <= 1+1e-8:
                continue
            value, u, n, v, M = shortcut(rho)
            Q = D.T@D
            delta = np.linalg.det(Q-s*I3)
            q = c@Q@(Q-s*I3)@c
            z = (Q-s*I3)@c
            J = (delta-q)*(Q-s*I3)
            V = J+np.outer(z,z)@Q
            record("rational_similarity", np.linalg.norm(
                np.linalg.solve(D, delta*(M-s*I3))@D-V))
            roots = np.linalg.eigvals(V)
            record("rational_root_imaginary", np.max(abs(roots.imag)))
            record("rational_cubic_value", alpha-min(roots.real)/delta-value)
            assert min(roots.real)>0
            margin = 1-(np.linalg.eigvalsh(M)[0]-s)/np.linalg.eigvalsh(K)[-1]-u@u
            assert margin > -1e-10
            count += 1

    rho=np.array([[20,0,0,14],[0,0,0,0],[0,0,7,0],[14,0,0,13]],complex)/40
    Rc=27/91
    Rs=13/21
    records=[]
    for R in [0, .05, .15, np.sqrt(27/539), .25, Rc, .4, .6, Rs, .8, 1.]:
        if R<=Rc:
            expected=49/50+(539/1350)*R*R
            u=np.array([-R*np.sqrt(max(0,1-(R/Rc)**2)),0,R*R/Rc])
        elif R<=Rs:
            expected=73/80+(91/200)*R-(147/400)*R*R
            u=np.array([0,0,R])
        else:
            expected=79/75
            u=np.array([0,0,Rs])
        actual=direct_filtered(rho,u)
        optimized,_=direct_max(rho,R,rng,starts=12)
        record("tilted_explicit_filter",actual-expected)
        record("tilted_direct_optimization",optimized-expected)
        records.append({"R":float(R),"expected":expected,"explicit_filter":actual,
                        "direct_optimizer":optimized,"effect":u.tolist()})

    # Exact symbolic rank-one determinant identity on the rational example.
    Rat=sp.Rational
    Q=sp.diag(Rat(49,100),Rat(49,100),Rat(169,400))
    c=sp.Matrix([0,0,Rat(7,20)])
    s=(c.T*c)[0]
    K=Q-s*sp.eye(3)
    delta=K.det()
    q=(c.T*Q*K*c)[0]
    z=K*c
    J=(delta-q)*K
    nu=sp.symbols("nu")
    P=(nu*sp.eye(3)-J).det()-(z.T*Q*(nu*sp.eye(3)-J).adjugate()*z)[0]
    assert sp.expand(P-(nu*sp.eye(3)-J-z*z.T*Q).det())==0
    polynomial=sp.factor(P)
    roots=list(sp.roots(P,nu).keys())
    assert min(roots)>0
    assert sp.simplify(sp.trace(Q)-s-min(roots)/delta-Rat(79,75))==0
    result={"seed":861704203,"rational_cubic_states":count,
            "frontier_cases":len(records),"maximum_residuals":residuals,
            "exact_polynomial":str(polynomial),"exact_positive_roots":[str(v) for v in roots],
            "frontier_records":records}
    Path(__file__).with_name("additional_exact_results.json").write_text(json.dumps(result,indent=2))
    print(json.dumps({k:v for k,v in result.items() if k!="frontier_records"},indent=2))


if __name__=="__main__":
    main()
