#!/usr/bin/env python3
"""Exact certificates and falsification tests for the tensor continuation.

This script does not numerically optimize a Schmidt number or a convex roof.
It checks the finite identities and explicit ensembles used in the written
proofs, followed by random ensemble checks of their universal matrix identity.
"""
from __future__ import annotations

import argparse
import json
import platform
from pathlib import Path

import numpy as np
import sympy as sp


def main() -> dict:
    exact: list[str] = []

    def check(name: str, condition: bool) -> None:
        if not bool(condition):
            raise AssertionError(name)
        exact.append(name)

    def zero(M: sp.MatrixBase) -> bool:
        return all(sp.simplify(v) == 0 for v in M)

    def vec(M: sp.MatrixBase) -> sp.Matrix:
        return sp.Matrix(list(M))

    def projector(v: sp.MatrixBase) -> sp.Matrix:
        return v * v.conjugate().T

    def partials(rho: sp.MatrixBase, d: int, e: int):
        ra = sp.Matrix(d, d, lambda i, j: sum(rho[i*e+k, j*e+k] for k in range(e)))
        rb = sp.Matrix(e, e, lambda i, j: sum(rho[k*e+i, k*e+j] for k in range(d)))
        return ra, rb

    def pt(rho: sp.MatrixBase, d: int, e: int):
        return sp.Matrix(d*e, d*e, lambda i, j:
            rho[(i//e)*e+j%e, (j//e)*e+i%e])

    A = sp.Matrix([[0, 1, 0], [0, 0, 1], [0, 0, 0]])
    B = sp.Matrix([[0, 0, 0], [1, 0, 0], [0, -1, 0]])
    I3 = sp.eye(3)
    aa, bb, cc, xx, yy, tt = sp.symbols("a b c x y t")
    check("nilpotent pencil cube for arbitrary complex coefficients", zero((aa*A+bb*B)**3))
    check("three dimensional determinant pencil", sp.expand((cc*I3+aa*A+bb*B).det()) == cc**3)
    gram = sp.Matrix([[sp.trace(C.conjugate().T*D) for D in (I3,A,B)] for C in (I3,A,B)])
    check("orthogonal support and normalization", gram == sp.diag(3,2,2))
    state = sum((projector(vec(C)) for C in (I3,A,B)), sp.zeros(9))/7
    check("state trace one", sp.trace(state) == 1)
    check("state rank three", state.rank() == 3)
    check("state nonzero spectrum", state.charpoly(tt).as_expr().factor() == tt**6*(7*tt-3)*(7*tt-2)**2/343)
    ra, rb = partials(state,3,3)
    check("actual Alice marginal", ra == sp.diag(2,3,2)/7)
    check("actual Bob marginal", rb == sp.diag(2,3,2)/7)
    check("flat roof coefficient weight", (vec(I3).T*state*vec(I3))[0]/9 == sp.Rational(1,7))
    check("Bell eigenvector and actual FEF witness", state*vec(I3) == sp.Rational(3,7)*vec(I3))
    ptchar = tt**2*(7*tt-1)**3*(7*tt-2)**2*(49*tt**2-3)/7**7
    check("partial transpose exact spectrum", sp.expand(pt(state,3,3).charpoly(tt).as_expr()-ptchar) == 0)
    marginal_cap = (sp.sqrt(3)+2*sp.sqrt(2))**2/21
    check("counterexample not a spectral FEF saturator", sp.simplify(marginal_cap-sp.Rational(3,7)).is_positive)

    AB = sp.kronecker_product(A,B)
    BA = sp.kronecker_product(B,A)
    K = sp.eye(9)+xx*AB+yy*BA
    check("nine dimensional determinant polynomial", sp.expand(K.det()-(xx*yy-1)**2*(2*xx*yy+1)) == 0)
    xn = sp.symbols("xn", nonzero=True)
    Kunit = K.subs({xx:xn,yy:1/xn})
    v1 = sp.zeros(9,1); v1[1] = -xn; v1[3] = 1
    v2 = sp.zeros(9,1); v2[5] = xn; v2[7] = 1
    check("first exact kernel vector", zero(Kunit*v1))
    check("second exact kernel vector", zero(Kunit*v2))
    check("kernel vectors independent", sp.Matrix.hstack(v1,v2).extract([3,7],[0,1]) == sp.eye(2))
    minor_ids = [0,1,2,4,5,6,8]
    check("rank seven minor", sp.simplify(Kunit.extract(minor_ids,minor_ids).det()) == 3)

    zeta = (-1+sp.sqrt(3)*sp.I)/2
    fourier = sp.Matrix(3,3,lambda i,j:zeta**(i*j)/sp.sqrt(3))
    check("Fourier replacement unitary", zero(fourier.conjugate().T*fourier-sp.eye(3)))
    replaced = [(sp.eye(9)+zeta**j*AB+zeta**(2*j)*BA)/sp.sqrt(3) for j in range(3)]
    old_three = [sp.eye(9),AB,BA]
    check("Fourier formula matches coefficient replacement", all(
        zero(replaced[j]-sum((fourier[j,k]*old_three[k] for k in range(3)),sp.zeros(9)))
        for j in range(3)))
    old_sum = sum((sp.SparseMatrix(projector(vec(C))) for C in old_three),sp.SparseMatrix(81,81,{}))
    new_sum = sum((sp.SparseMatrix(projector(vec(C))) for C in replaced),sp.SparseMatrix(81,81,{}))
    check("actual 81 dimensional Fourier ensemble equality", zero(new_sum-old_sum))
    check("three replaced vector probabilities", all(sp.simplify(sp.trace(C.conjugate().T*C)/49-sp.Rational(17,147)) == 0 for C in replaced))
    remaining = [sp.kronecker_product(C,D) for C,D in
        ((I3,A),(I3,B),(A,I3),(B,I3),(A,A),(B,B))]
    check("remaining exact Schmidt ranks", [C.rank() for C in remaining] == [6,6,6,6,4,4])
    weights = [sp.Rational(17,147)]*3+[sp.Rational(6,49)]*4+[sp.Rational(4,49)]*2
    check("nine term probabilities sum one", sum(weights) == 1)
    check("all Fourier coefficients have xy one", all(sp.simplify(zeta**j*zeta**(2*j)-1) == 0 for j in range(3)))
    check("product eigenensemble assistance lower value", sp.Rational(3,7)**2 == sp.Rational(9,49))
    check("strict two copy Schmidt loss and filtering gap", 7 < 3**2 and sp.sqrt(7)/3 < 1)

    pp = sp.symbols("p", real=True)
    family = pp*projector(vec(I3))/3+(1-pp)*(projector(vec(A))+projector(vec(B)))/4
    tail = (projector(vec(A))+projector(vec(B)))/4
    bell3 = projector(vec(I3))/3
    qlo = 7*pp/3
    qhi = (7*pp-3)/4
    check("parameter family trace one", sp.simplify(sp.trace(family)) == 1)
    check("parameter family exact flat roof coefficient", sp.simplify((vec(I3).T*family*vec(I3))[0]/9-pp/3) == 0)
    check("parameter family lower interval mixture", zero(family-qlo*state-(1-qlo)*tail))
    check("parameter family upper interval mixture", zero(family-qhi*bell3-(1-qhi)*state))
    check("parameter family quadratic roof upper bound", sp.simplify(qhi**2+sp.Rational(6,7)*qhi*(1-qhi)-(7*pp-3)*(pp+3)/16) == 0)
    check("parameter family strict multiplicativity deficit", sp.simplify(pp**2-(7*pp-3)*(pp+3)/16-sp.Rational(9,16)*(1-pp)**2) == 0)
    ratio = sp.Rational(3,4)*(1-pp)/pp
    check("parameter family exact operator comparison and filtering join",
        zero(family-7*(1-pp)*state/4-(7*pp-3)*projector(vec(I3))/12)
        and zero(7*pp*state/3-family-(7*pp-3)*(projector(vec(A))+projector(vec(B)))/12)
        and sp.simplify(ratio-(7*(1-pp)/4)/(7*pp/3)) == 0
        and sp.simplify((1-ratio*(1-sp.sqrt(7)/3)).subs(pp,sp.Rational(3,7))-sp.sqrt(7)/3) == 0)

    # The non-triangular nilpotent pencil does not remain nilpotent under
    # matrix amplification, even though every scalar pencil is nilpotent.
    E01 = sp.Matrix([[0,1],[0,0]])
    amplified = sp.kronecker_product(A,E01)+sp.kronecker_product(B,E01.T)
    check("amplified pencil characteristic polynomial", sp.expand(amplified.charpoly(tt).as_expr()-tt**2*(tt-1)*(tt+1)*(tt**2+1)) == 0)

    # Exact spectral-saturation nonclosure under tensor products.
    Z = sp.diag(sp.Rational(3,4),sp.Rational(1,4))
    N = sp.sqrt(6)/4*E01
    saturator = projector(vec(Z))+projector(vec(N))
    sa,sb = partials(saturator,2,2)
    check("saturator actual marginals", sa == sp.diag(15,1)/16 and sb == sp.diag(9,7)/16)
    check("saturator spectrum", saturator.charpoly(tt).as_expr().factor() == tt**2*(8*tt-5)*(8*tt-3)/64)
    a2 = [sp.Rational(i,256) for i in (225,15,15,1)]
    b2 = [sp.Rational(i,256) for i in (81,63,63,49)]
    check("tensor square cap strictly larger than spectral norm", sum(min(a,b) for a,b in zip(a2,b2)) == sp.Rational(7,16) > sp.Rational(25,64))

    # Exact lower/upper roof ensembles for the arbitrary second factor.
    P = [sp.Matrix([[0,1],[1,0]]),sp.Matrix([[0,-sp.I],[sp.I,0]]),sp.diag(1,-1)]
    six = [(sp.sqrt(3)*sp.eye(2)+sign*pauli)/(2*sp.sqrt(2)) for pauli in P for sign in (-1,1)]
    phi = vec(sp.eye(2))/sp.sqrt(2)
    sigma = sp.Rational(3,4)*projector(phi)+sp.Rational(1,12)*(sp.eye(4)-projector(phi))
    check("isotropic six vector ensemble exact", zero(sum((projector(vec(C))/6 for C in six),sp.zeros(4))-sigma))
    check("all six pure vectors normalized", all(sp.simplify(sp.trace(C.conjugate().T*C)) == 1 for C in six))
    check("all six pure concurrences one half", all(sp.simplify(2*sp.Abs(C.det())) == sp.Rational(1,2) for C in six))
    check("tensor isotropic convex roof exact candidate", 2*Z.det()*sp.Rational(1,2) == sp.Rational(3,16))
    check("tensor isotropic assistance exact candidate", 2*Z.det() == sp.Rational(3,8))

    # General 2-by-2 block determinant identity, with a fully arbitrary
    # second-factor coefficient matrix and arbitrary off-diagonal block.
    d0,d1 = sp.symbols("d0 d1")
    c00,c01,c10,c11,n00,n01,n10,n11 = sp.symbols("c00 c01 c10 c11 n00 n01 n10 n11")
    C0 = sp.Matrix([[c00,c01],[c10,c11]])
    Q = sp.Matrix([[n00,n01],[n10,n11]])
    T = sp.BlockMatrix([[d0*C0,Q],[sp.zeros(2),d1*C0]]).as_explicit()
    check("arbitrary complex block determinant certificate", sp.expand(T.det()-(d0*d1)**2*C0.det()**2) == 0)

    rng = np.random.default_rng(7326)
    def unitary(n: int):
        q,r = np.linalg.qr(rng.normal(size=(n,n))+1j*rng.normal(size=(n,n)))
        phase=np.diag(r); return q*(phase/np.abs(phase)).conj()
    def gn(C: np.ndarray):
        dim=C.shape[0]
        return dim*abs(np.linalg.det(C))**(2/dim)
    def npa(C):
        return np.array(C.evalf(),dtype=np.complex128)
    flat_basis=np.column_stack([npa(vec(C)).ravel()/np.sqrt(7) for C in (I3,A,B)])
    max_flat_error=0.0
    for _ in range(200):
        ensemble=flat_basis@unitary(3)
        val=sum(gn(ensemble[:,j].reshape(3,3)) for j in range(3))
        max_flat_error=max(max_flat_error,abs(val-3/7))
    assert max_flat_error<1e-12

    bell=[np.eye(2,dtype=complex)/np.sqrt(2)]+[npa(pauli)/np.sqrt(2) for pauli in P]
    sigma_probs=[3/4,1/12,1/12,1/12]
    tensor_basis=np.column_stack([np.kron(npa(C),D*np.sqrt(prob)).ravel()
        for C in (Z,N) for D,prob in zip(bell,sigma_probs)])
    sigma_np=npa(sigma)
    max_roof_identity_error=0.0
    max_induced_ensemble_error=0.0
    smallest_roof=1.0
    largest_roof=0.0
    for _ in range(300):
        ensemble=tensor_basis@unitary(8)
        lower=0.0; upper=0.0; induced=np.zeros((4,4),dtype=complex)
        for j in range(8):
            tensor=ensemble[:,j].reshape(4,4)
            core=(.75*tensor[:2,:2]+.25*tensor[2:,2:])/(5/8)
            lower+=gn(tensor); upper+=(3/8)*gn(core)
            corevec=core.ravel(); induced+=np.outer(corevec,corevec.conj())
        max_roof_identity_error=max(max_roof_identity_error,abs(lower-upper))
        max_induced_ensemble_error=max(max_induced_ensemble_error,float(np.max(np.abs(induced-sigma_np))))
        smallest_roof=min(smallest_roof,lower); largest_roof=max(largest_roof,lower)
        assert 3/16-1e-12<=lower<=3/8+1e-12
    assert max_roof_identity_error<1e-12
    assert max_induced_ensemble_error<1e-12

    # Rank bounds for arbitrary rectangular coefficient blocks and arbitrary
    # upper triangular quantum residual amplitudes. These are falsification
    # tests; the exact minor argument is the universal proof.
    rank_tests=0
    for d in range(2,6):
        for e,f in ((2,2),(2,3),(3,2),(3,4)):
            for k in range(1,min(e,f)+1):
                for _ in range(8):
                    core=(rng.normal(size=(e,k))+1j*rng.normal(size=(e,k)))@(rng.normal(size=(k,f))+1j*rng.normal(size=(k,f)))
                    diagonal=rng.uniform(.2,1,size=d)
                    tensor=np.kron(np.diag(diagonal),core)
                    for i in range(d):
                        for j in range(i+1,d):
                            tensor[i*e:(i+1)*e,j*f:(j+1)*f]+=rng.normal(size=(e,f))+1j*rng.normal(size=(e,f))
                    assert np.linalg.matrix_rank(tensor,tol=1e-9)>=d*k
                    rank_tests+=1

    return {
        "status":"passed",
        "scope":"Exact matrix/ensemble certificates and numerical falsification tests; no numerical convex-roof or Schmidt-number solver.",
        "versions":{"python":platform.python_version(),"numpy":np.__version__,"sympy":sp.__version__},
        "exact_certificate_count":len(exact),
        "exact_certificates":exact,
        "random_flat_roof_ensembles":200,
        "max_flat_roof_error":max_flat_error,
        "random_arbitrary_second_factor_ensembles":300,
        "max_universal_roof_identity_error":max_roof_identity_error,
        "max_induced_ensemble_reconstruction_error":max_induced_ensemble_error,
        "observed_roof_interval":[smallest_roof,largest_roof],
        "rectangular_rank_tests":rank_tests,
        "counterexample":{"single_G":"3/7","single_assistance":"3/7","single_Schmidt_number":3,
            "tensor_G":0,"tensor_Schmidt_number_upper_bound":7,"tensor_assistance_lower_bound":"9/49",
            "one_copy_stochastic_LOCC_FEF_upper_bound":"sqrt(7)/3",
            "exact_tensor_Schmidt_number_claimed":False},
        "parameter_family":{"single_G":"p","single_assistance":"p",
            "tensor_G_upper_bound":"max(0, p^2 - 9(1-p)^2/16)",
            "tensor_G_zero_interval":"0 < p <= 3/7",
            "strict_tensor_G_submultiplicativity":"0 < p < 1",
            "stochastic_LOCC_FEF_upper_bound_low_p":"sqrt(7)/3 for 0 < p <= 3/7",
            "stochastic_LOCC_FEF_upper_bound_high_p":"1 - 3(1-p)/(4p) * (1-sqrt(7)/3) for 3/7 <= p < 1",
            "upper_bound_claimed_exact_above_3_over_7":False},
    }


if __name__ == "__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument("--output",type=Path,default=Path(__file__).with_suffix(".json"))
    args=parser.parse_args()
    result=main()
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps(result,indent=2))
