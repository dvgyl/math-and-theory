#!/usr/bin/env python3
"""Independent checks for the fully-entangled-fraction saturation package.

Written separately from the uploaded analysis scripts. It recomputes the
central finite statements from their definitions:

  * the two-qubit joint frontier F(c,b), its attaining states, the deficit
    identity, the Milne saturators and the optimal stability coefficient;
  * random-state falsification tests of f <= F(c,b) and of the stability bound;
  * the three-level nilpotent counterexample (exact, with SymPy);
  * the tensor-saturator and isotropic-state examples;
  * the collective coupling fixture, cross-checked against an SDP;
  * the Hermitian rank counterexample used to show that positivity is needed;
  * the weighted marginal-spectrum bound and the spectral cap on f_d in
    dimensions three and four, and attainment by the coherent-minimum state.

Exact identities are checked symbolically. Numerical checks are falsification
tests only, never proofs. Usage: python3 -I independent_check.py [--output FILE]
"""
import argparse
import json
import sys

import numpy as np
import sympy as sp

RESULTS = []


def record(name, ok, detail=""):
    RESULTS.append({"check": name, "passed": bool(ok), "detail": detail})
    print(("PASS " if ok else "FAIL ") + name + ((" : " + detail) if detail else ""))


# ---------------------------------------------------------------- two qubits
I2 = np.eye(2)
PX = np.array([[0, 1], [1, 0]], dtype=complex)
PY = np.array([[0, -1j], [1j, 0]], dtype=complex)
PZ = np.array([[1, 0], [0, -1]], dtype=complex)
PAULI = [PX, PY, PZ]
# magic basis (columns)
MAGIC = np.array([[1, 0, 0, 1j], [0, 1j, 1, 0], [0, 1j, -1, 0], [1, 0, 0, -1j]], dtype=complex) / np.sqrt(2)


def bloch(rho):
    a = np.array([np.trace(rho @ np.kron(P, I2)).real for P in PAULI])
    b = np.array([np.trace(rho @ np.kron(I2, P)).real for P in PAULI])
    T = np.array([[np.trace(rho @ np.kron(P, Q)).real for Q in PAULI] for P in PAULI])
    return a, b, T


def centre(rho):
    a, b, T = bloch(rho)
    nb = np.linalg.norm(b)
    if abs(nb - 1) < 1e-12:
        return a, nb
    return (a - T @ b) / (1 - nb ** 2), nb


def fef_magic(rho):
    """Two-qubit FEF = largest eigenvalue of Re(rho) in the magic basis."""
    rm = MAGIC.conj().T @ rho @ MAGIC
    return float(np.linalg.eigvalsh(rm.real).max())


def fef_search(rho, rng, trials=4000):
    """Direct lower estimate: max over U of <Phi_U|rho|Phi_U>."""
    best = 0.0
    phi = np.array([1, 0, 0, 1]) / np.sqrt(2)
    for _ in range(trials):
        z = rng.normal(size=(2, 2)) + 1j * rng.normal(size=(2, 2))
        q, r = np.linalg.qr(z)
        v = np.kron(I2, q) @ phi
        best = max(best, (v.conj() @ rho @ v).real)
    return best


def frontier(c, b):
    return (np.sqrt(1 + b) + np.sqrt((1 - c) * (1 - b))) ** 2 / 4


def random_state(rng, kind):
    if kind == "full":
        g = rng.normal(size=(4, 4)) + 1j * rng.normal(size=(4, 4))
    else:
        k = {"rank1": 1, "rank2": 2, "rank3": 3}[kind]
        g = rng.normal(size=(4, k)) + 1j * rng.normal(size=(4, k))
    rho = g @ g.conj().T
    if rng.random() < 0.5:  # random Bob filter to spread the Bob length
        f = rng.normal(size=(2, 2)) + 1j * rng.normal(size=(2, 2))
        F = np.kron(I2, f)
        rho = F @ rho @ F.conj().T
    return rho / np.trace(rho).real


def two_qubit_checks(rng):
    c, b = sp.symbols("c b", nonnegative=True)
    F = (sp.sqrt(1 + b) + sp.sqrt((1 - c) * (1 - b))) ** 2 / 4
    D = (sp.sqrt(1 - b) - sp.sqrt((1 - c) * (1 + b))) ** 2 / 4
    # exact check with s = sqrt(1+b), t = sqrt(1-b), w = sqrt(1-c), all >= 0
    s_, t_, w_ = sp.symbols("s t w", nonnegative=True)
    Fs = (s_ + w_ * t_) ** 2 / 4
    Ds = (t_ - w_ * s_) ** 2 / 4
    gap = sp.expand(sp.Rational(1, 2) * (1 + w_ ** 2) - Fs - Ds).subs(t_ ** 2, 2 - s_ ** 2)
    record("deficit identity 1-c/2-F = D", sp.expand(gap) == 0)
    # equality point
    bstar = c / (2 - c)
    val = sp.simplify((1 - bstar) - (1 - c) * (1 + bstar))
    record("deficit vanishes at b = c/(2-c)", val == 0)
    # stability algebra: ((2-c)b-c)^2 = 4 (u+v)^2 D with u=sqrt(1-b), v=sqrt(1-c)sqrt(1+b)
    u, v = sp.sqrt(1 - b), sp.sqrt(1 - c) * sp.sqrt(1 + b)
    lhs = ((2 - c) * b - c) ** 2
    rhs = 4 * (u + v) ** 2 * (u - v) ** 2 / 4
    record("stability identity ((2-c)b-c)^2 = (u+v)^2 (u-v)^2", sp.simplify(sp.expand(lhs - rhs)) == 0)

    # attaining states, exact
    ok_all = True
    for cv, bv in [(sp.Rational(3, 5), sp.Rational(1, 3)), (sp.Rational(1, 2), 0), (sp.Rational(1, 7), sp.Rational(5, 6)),
                   (0, sp.Rational(2, 5)), (1, sp.Rational(1, 4))]:
        vvec = sp.Matrix([sp.sqrt(1 + bv), 0, 0, sp.sqrt((1 - cv) * (1 - bv))])
        rho = vvec * vvec.T / 2
        rho[1, 1] += cv * (1 - bv) / 2
        tr = sp.simplify(rho.trace())
        phi = sp.Matrix([1, 0, 0, 1]) / sp.sqrt(2)
        ov = sp.simplify((phi.T * rho * phi)[0])
        target = sp.simplify(F.subs({c: cv, b: bv}))
        rn = np.array(rho.evalf(30).tolist(), dtype=complex)
        cen, nb = centre(rn)
        ok = (tr == 1 and sp.simplify(ov - target) == 0 and abs(np.linalg.norm(cen) - float(cv)) < 1e-12
              and abs(nb - float(bv)) < 1e-12 and abs(fef_magic(rn) - float(target)) < 1e-12
              and np.linalg.eigvalsh(rn).min() > -1e-14)
        ok_all &= ok
    record("joint-frontier states rho_{c,b}: trace, centre, Bob length, FEF = F(c,b)", ok_all)

    # Milne saturator representative
    ok_all = True
    for cv in [0.0, 0.2, 0.5, 0.9, 1.0]:
        chi = np.array([1, 0, 0, 1 - cv])
        rho = (np.outer(chi, chi) + cv * (1 - cv) * np.diag([0, 1, 0, 0])) / (2 - cv)
        cen, nb = centre(rho)
        ok_all &= abs(np.linalg.norm(cen) - cv) < 1e-12 and abs(fef_magic(rho) - (1 - cv / 2)) < 1e-12
        ok_all &= abs(nb - (cv / (2 - cv))) < 1e-12 or cv == 1.0
    record("Milne saturators rho_c: centre c, FEF 1-c/2, Bob length c/(2-c)", ok_all)

    # FEF formula sanity: magic-basis eigenvalue vs direct search
    worst = 0.0
    for _ in range(20):
        rho = random_state(rng, "full")
        worst = max(worst, fef_search(rho, rng) - fef_magic(rho))
    record("direct search never exceeds magic-basis FEF", worst < 1e-9, f"max excess {worst:.2e}")

    # random falsification of f <= F(c,b) and optimal stability
    worst_f = -1.0
    worst_milne = -1.0
    worst_stab = -1.0
    n = 0
    for kind in ["full", "rank1", "rank2", "rank3"]:
        for _ in range(5000):
            rho = random_state(rng, kind)
            cen, nb = centre(rho)
            cc = min(np.linalg.norm(cen), 1.0)
            f = fef_magic(rho)
            worst_milne = max(worst_milne, f - (1 - cc / 2))
            if nb < 1 - 1e-9:
                worst_f = max(worst_f, f - frontier(cc, nb))
            K = 4 * (1 + np.sqrt(1 - cc)) ** 2
            eps = 1 - cc / 2 - f
            worst_stab = max(worst_stab, ((2 - cc) * nb - cc) ** 2 - K * eps)
            n += 1
    record("random states: f <= F(c,b)", worst_f < 1e-9, f"{n} states, max violation {worst_f:.2e}")
    record("random states: f <= 1-c/2", worst_milne < 1e-9, f"max violation {worst_milne:.2e}")
    record("random states: ((2-c)b-c)^2 <= K(c) eps", worst_stab < 1e-8, f"max violation {worst_stab:.2e}")

    # optimal coefficient attained at b=0 frontier state, c>0
    ok = True
    for cv in [0.1, 0.4, 0.8]:
        ratio = cv ** 2 / (1 - cv / 2 - frontier(cv, 0.0))
        ok &= abs(ratio - 4 * (1 + np.sqrt(1 - cv)) ** 2) < 1e-9
    record("stability coefficient K(c) attained by b=0 frontier state", ok)

    # strict exact ellipsoid example
    rho = np.array([[18 / 25, 0, 0, 4 / 25], [0, 7 / 50, 0, 0], [0, 0, 2 / 25, 0], [4 / 25, 0, 0, 3 / 50]])
    cen, nb = centre(rho)
    record("signed-ellipsoid example: f = 11/20 at c = 3/5", abs(fef_magic(rho) - 11 / 20) < 1e-12
           and abs(np.linalg.norm(cen) - 0.6) < 1e-12, f"f={fef_magic(rho):.12f}")


# --------------------------------------------------------- nilpotent example
def nilpotent_checks():
    A = sp.Matrix([[0, 1, 0], [0, 0, 1], [0, 0, 0]])
    B = sp.Matrix([[0, 0, 0], [1, 0, 0], [0, -1, 0]])
    I3 = sp.eye(3)
    a, b, cc, x, y = sp.symbols("a b c x y")

    def vec(C):
        return sp.Matrix([C[i, j] for i in range(C.rows) for j in range(C.cols)])

    omega = (vec(I3) * vec(I3).T + vec(A) * vec(A).T + vec(B) * vec(B).T) / 7
    record("omega trace one", omega.trace() == 1)
    ev = omega.eigenvals()
    record("omega spectrum 3/7, 2/7, 2/7, 0^6",
           ev == {sp.Rational(3, 7): 1, sp.Rational(2, 7): 2, 0: 6})
    record("(aA+bB)^3 = 0", sp.expand((a * A + b * B) ** 3) == sp.zeros(3))
    record("det(cI + aA + bB) = c^3", sp.expand((cc * I3 + a * A + b * B).det() - cc ** 3) == 0)
    # marginals
    rA = sp.zeros(3)
    rB = sp.zeros(3)
    for i in range(3):
        for k in range(3):
            rA[i, k] = sum(omega[3 * i + j, 3 * k + j] for j in range(3))
            rB[i, k] = sum(omega[3 * j + i, 3 * j + k] for j in range(3))
    record("omega marginals diag(2,3,2)/7", rA == sp.diag(2, 3, 2) / 7 and rB == sp.diag(2, 3, 2) / 7)
    # partial transpose spectrum
    pt = sp.zeros(9)
    for i in range(3):
        for j in range(3):
            for k in range(3):
                for l in range(3):
                    pt[3 * i + j, 3 * k + l] = omega[3 * i + l, 3 * k + j]
    pev = pt.eigenvals()
    expect = {sp.Rational(1, 7): 3, sp.Rational(2, 7): 2, 0: 2, sp.sqrt(3) / 7: 1, -sp.sqrt(3) / 7: 1}
    record("partial-transpose spectrum", {sp.nsimplify(k): v for k, v in pev.items()} == expect, str(pev))
    # sharp marginal cap
    cap = sp.simplify((sp.sqrt(sp.Rational(3, 7)) + 2 * sp.sqrt(sp.Rational(2, 7))) ** 2 / 3)
    record("marginal-spectrum FEF cap (11+4 sqrt6)/21 > 3/7",
           sp.simplify(cap - (11 + 4 * sp.sqrt(6)) / 21) == 0 and cap > sp.Rational(3, 7))
    # Kronecker determinant identity and kernel
    AB, BA, I9 = sp.kronecker_product(A, B), sp.kronecker_product(B, A), sp.eye(9)
    M = I9 + x * AB + y * BA
    record("det(I9 + x A(x)B + y B(x)A) = (xy-1)^2 (2xy+1)",
           sp.expand(M.det() - (x * y - 1) ** 2 * (2 * x * y + 1)) == 0)
    # ensemble
    z = sp.Rational(-1, 2) + sp.sqrt(3) * sp.I / 2
    mats = [I3, A, B]
    target = sp.zeros(81)
    for C in mats:
        for Dm in mats:
            v = vec(sp.kronecker_product(C, Dm))
            target += v * v.T
    target /= 49
    ens = []
    for j in range(3):
        ens.append((I9 + z ** j * AB + z ** (2 * j) * BA) / sp.sqrt(3))
    rest = [sp.kronecker_product(I3, A), sp.kronecker_product(I3, B), sp.kronecker_product(A, I3),
            sp.kronecker_product(B, I3), sp.kronecker_product(A, A), sp.kronecker_product(B, B)]
    ens += rest
    S = sp.zeros(81)
    for C in ens:
        v = vec(C)
        S += v * v.conjugate().T
    S /= 49
    record("nine-term Fourier ensemble sums exactly to omega (x) omega",
           (S - target).applyfunc(lambda e: sp.expand(e)) == sp.zeros(81))
    ranks = [sp.Matrix(sp.simplify(C)).rank(simplify=True) for C in ens]
    dets = [sp.simplify(sp.expand(C.det())) for C in ens]
    record("ensemble ranks 7,7,7,6,6,6,6,4,4 and all determinants zero",
           ranks == [7, 7, 7, 6, 6, 6, 6, 4, 4] and all(d == 0 for d in dets), str(ranks))
    probs = [sp.nsimplify(sp.simplify((vec(C).conjugate().T * vec(C))[0] / 49)) for C in ens]
    record("ensemble probabilities 17/147 (x3), 6/49 (x4), 4/49 (x2), total one",
           probs == [sp.Rational(17, 147)] * 3 + [sp.Rational(6, 49)] * 4 + [sp.Rational(4, 49)] * 2
           and sum(probs) == 1, str(probs))
    # rank-seven principal minor of the Fourier matrix at xy = 1
    Mx = (I9 + x * AB + (1 / x) * BA)
    minor = sp.simplify(Mx.extract([0, 1, 2, 4, 5, 6, 8], [0, 1, 2, 4, 5, 6, 8]).det())
    record("principal minor {0,1,2,4,5,6,8} has determinant 3 when xy = 1", minor == 3, str(minor))
    # omega_p family identities
    p = sp.symbols("p", positive=True)
    q = (7 * p - 3) / 4
    record("upper roof identity q^2 + 6/7 q(1-q) = p^2 - 9/16 (1-p)^2",
           sp.expand(q ** 2 + sp.Rational(6, 7) * q * (1 - q) - (p ** 2 - sp.Rational(9, 16) * (1 - p) ** 2)) == 0)
    P3 = vec(I3) * vec(I3).T / 3
    T = (vec(A) * vec(A).T + vec(B) * vec(B).T) / 4
    omp = p * P3 + (1 - p) * T
    record("omega_p = q P3 + (1-q) omega", sp.simplify(omp - (q * P3 + (1 - q) * omega)) == sp.zeros(9))
    record("omega_p = (7p/3) omega + (1-7p/3) T",
           sp.simplify(omp - (7 * p / 3 * omega + (1 - 7 * p / 3) * T)) == sp.zeros(9))


# ------------------------------------------------ tensor-saturator examples
def tensor_examples():
    zv = np.array([3, 0, 0, 1]) / 4
    rho = np.outer(zv, zv) + 3 / 8 * np.diag([0, 1, 0, 0])
    ra = np.array([[rho[0, 0] + rho[1, 1], 0], [0, rho[2, 2] + rho[3, 3]]])
    rb = np.array([[rho[0, 0] + rho[2, 2], 0], [0, rho[1, 1] + rho[3, 3]]])
    alpha = np.sort(np.diag(ra))[::-1]
    beta = np.sort(np.diag(rb))[::-1]
    ok = np.allclose(alpha, [15 / 16, 1 / 16]) and np.allclose(beta, [9 / 16, 7 / 16])
    cap = 0.5 * (np.sqrt(min(alpha[0], beta[0])) + np.sqrt(min(alpha[1], beta[1]))) ** 2
    ok &= abs(fef_magic(rho) - 0.5) < 1e-12 and abs(cap - 0.5) < 1e-12
    lam2 = np.linalg.eigvalsh(np.kron(rho, rho)).max()
    a2 = np.sort(np.kron(alpha, alpha))[::-1]
    b2 = np.sort(np.kron(beta, beta))[::-1]
    ok &= abs(lam2 - 25 / 64) < 1e-12 and abs(np.minimum(a2, b2).sum() - 7 / 16) < 1e-12
    record("rho_* is a spectral saturator whose tensor square is not", ok)
    # isotropic six-vector ensemble
    phi = np.array([1, 0, 0, 1]) / np.sqrt(2)
    P = np.outer(phi, phi)
    sigma = 0.75 * P + (np.eye(4) - P) / 12
    S = np.zeros((4, 4), dtype=complex)
    conc = []
    for Pj in PAULI:
        for s in (1, -1):
            C = (np.sqrt(3) * I2 + s * Pj) / (2 * np.sqrt(2))
            v = C.reshape(4)
            S += np.outer(v, v.conj()) / 6
            conc.append(2 * abs(np.linalg.det(C)))
    record("isotropic six-vector ensemble reproduces sigma with concurrence 1/2 each",
           np.allclose(S, sigma) and np.allclose(conc, 0.5))


# ------------------------------------------------ collective coupling fixture
def collective_checks():
    s21 = sp.sqrt(21)
    a = [sp.Rational(7, 10), sp.Rational(3, 10)]
    b = [sp.Rational(3, 10), sp.Rational(7, 10)]
    p = [sp.Rational(1, 2)] * 2
    import itertools

    def Cn(n):
        tot = 0
        for idx in itertools.product(range(2), repeat=n):
            U = sp.prod([sp.sqrt(p[i] * a[i]) for i in idx])
            V = sp.prod([sp.sqrt(p[i] * b[i]) for i in idx])
            tot += sp.Min(U, V)
        return sp.nsimplify(sp.expand(tot ** 2))

    C1, C2, C3 = Cn(1), Cn(2), Cn(3)
    record("C1 = 3/5", sp.simplify(C1 - sp.Rational(3, 5)) == 0)
    record("C2 = (15+3 sqrt21)/50 > 9/25", sp.simplify(C2 - (15 + 3 * s21) / 50) == 0 and C2 > sp.Rational(9, 25))
    record("C3 = (297+27 sqrt21)/1000 and C2^3 > C3^2",
           sp.simplify(C3 - (297 + 27 * s21) / 1000) == 0
           and sp.simplify(C2 ** 3 - C3 ** 2 - (2349 * s21 - 4239) / 500000) == 0 and C2 ** 3 > C3 ** 2)
    kappa2 = (2 * (sp.Rational(35, 100) * sp.Rational(15, 100)) ** sp.Rational(1, 4)) ** 2
    record("regularized value kappa^2 = sqrt21/5", sp.simplify(kappa2 - s21 / 5) == 0)
    # SDP cross-check of C1 and C2 (fixed marginals, fixed target)
    try:
        import cvxpy as cp
    except ImportError:
        record("SDP cross-check skipped (cvxpy missing)", True)
        return
    for n, exact in [(1, float(C1)), (2, float(C2))]:
        an = np.array([0.7, 0.3])
        bn = np.array([0.3, 0.7])
        A = np.diag(an)
        B = np.diag(bn)
        for _ in range(n - 1):
            A = np.kron(A, np.diag(an))
            B = np.kron(B, np.diag(bn))
        d = A.shape[0]
        xv = np.zeros(d * d)
        x1 = np.zeros(4)
        x1[0] = x1[3] = 1 / np.sqrt(2)
        # x^{(x) n} regrouped A1..An : B1..Bn
        X1 = np.eye(2) / np.sqrt(2)
        X = X1
        for _ in range(n - 1):
            X = np.kron(X, X1)
        xv = X.reshape(d * d)
        R = cp.Variable((d * d, d * d), hermitian=True)
        cons = [R >> 0, cp.partial_trace(R, [d, d], axis=1) == A, cp.partial_trace(R, [d, d], axis=0) == B]
        prob = cp.Problem(cp.Maximize(cp.real(xv @ R @ xv)), cons)
        prob.solve(solver=cp.CLARABEL)
        record(f"SDP value for C{n} agrees with exact formula", abs(prob.value - exact) < 1e-6,
               f"sdp={prob.value:.8f} exact={exact:.8f}")


def rank_counterexample():
    M = np.diag([2.0, -1.0, -1.0, 1.0])
    ra = np.array([M[0, 0] + M[1, 1], M[2, 2] + M[3, 3]])
    rb = np.array([M[0, 0] + M[2, 2], M[1, 1] + M[3, 3]])
    record("Hermitian diag(2,-1,-1,1): trace one, marginals diag(1,0), rank four",
           np.trace(M) == 1 and np.allclose(ra, [1, 0]) and np.allclose(rb, [1, 0]) and np.linalg.matrix_rank(M) == 4)


# ------------------------------------------- higher-dimensional spectral cap
def _partial_traces(rho, d):
    r = rho.reshape(d, d, d, d)
    return np.einsum("ijkj->ik", r), np.einsum("ijil->jl", r)


def _fef_search(rho, d, rng, starts=12):
    """Lower estimate of f_d by local maximization over Bob unitaries."""
    from scipy.linalg import expm
    from scipy.optimize import minimize
    phi = np.eye(d).reshape(d * d) / np.sqrt(d)
    n = d * d

    def unitary(p):
        h = np.zeros((d, d), dtype=complex)
        iu = np.triu_indices(d, 1)
        k = len(iu[0])
        h[iu] = p[:k] + 1j * p[k:2 * k]
        h = h + h.conj().T + np.diag(p[2 * k:])
        return expm(1j * h)

    def value(p):
        e = np.kron(np.eye(d), unitary(p)) @ phi
        return -np.real(e.conj() @ rho @ e)

    best = 0.0
    for _ in range(starts):
        res = minimize(value, rng.normal(size=n), method="BFGS")
        best = max(best, -res.fun)
    return best


def highdim_checks(rng):
    """Spectral cap f_d <= (1/d)(sum sqrt(min(alpha_i, beta_i)))^2 and the weighted bound."""
    worst_weighted, worst_cap, gap_attained = -1.0, -1.0, 0.0
    for d in (3, 4):
        for trial in range(12):
            rank = 1 + trial % (d * d)
            g = rng.normal(size=(d * d, rank)) + 1j * rng.normal(size=(d * d, rank))
            rho = g @ g.conj().T
            rho /= np.trace(rho).real
            ra, rb = _partial_traces(rho, d)
            al = np.sort(np.linalg.eigvalsh(ra))[::-1]
            be = np.sort(np.linalg.eigvalsh(rb))[::-1]
            m = np.minimum(al, be).clip(min=0)
            # weighted bound for random targets
            for _ in range(20):
                x = rng.normal(size=d * d) + 1j * rng.normal(size=d * d)
                x /= np.linalg.norm(x)
                s = np.linalg.svd(x.reshape(d, d), compute_uv=False)
                worst_weighted = max(worst_weighted, np.real(x.conj() @ rho @ x) - np.dot(s, np.sqrt(m)) ** 2)
            if trial < 4:
                cap = np.sum(np.sqrt(m)) ** 2 / d
                worst_cap = max(worst_cap, _fef_search(rho, d, rng) - cap)
        # coherent-minimum construction attains the cap
        al = rng.dirichlet(np.ones(d)); al = np.sort(al)[::-1]
        be = rng.dirichlet(np.ones(d)); be = np.sort(be)[::-1]
        m = np.minimum(al, be); u = al - m; v = be - m; delta = 1 - m.sum()
        z = np.zeros(d * d); z[[i * d + i for i in range(d)]] = np.sqrt(m)
        tau = np.outer(z, z).astype(complex)
        if delta > 1e-12:
            tau += np.diag(np.outer(u, v).reshape(d * d) / delta)
        ra, rb = _partial_traces(tau, d)
        ok_marg = np.allclose(np.diag(ra), al) and np.allclose(np.diag(rb), be)
        cap = np.sum(np.sqrt(m)) ** 2 / d
        found = _fef_search(tau, d, rng)
        gap_attained = max(gap_attained, abs(found - cap))
        record(f"d={d}: coherent-minimum state has the prescribed marginals and f_d equal to the cap",
               ok_marg and abs(found - cap) < 1e-7, f"cap={cap:.10f} search={found:.10f}")
    record("weighted prescribed-Schmidt bound never violated (d=3,4; 480 random targets)",
           worst_weighted < 1e-12, f"max excess {worst_weighted:.2e}")
    record("local search for f_d never exceeds the marginal-spectrum cap (d=3,4)",
           worst_cap < 1e-9, f"max excess {worst_cap:.2e}")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", default=None)
    ap.add_argument("--seed", type=int, default=20261103)
    args = ap.parse_args()
    rng = np.random.default_rng(args.seed)
    two_qubit_checks(rng)
    nilpotent_checks()
    tensor_examples()
    collective_checks()
    rank_counterexample()
    highdim_checks(rng)
    ok = all(r["passed"] for r in RESULTS)
    out = {"all_passed": ok, "seed": args.seed, "checks": RESULTS,
           "versions": {"python": sys.version.split()[0], "numpy": np.__version__, "sympy": sp.__version__},
           "scope": "Exact symbolic identities and seeded numerical falsification tests; not a proof of the universal theorems."}
    if args.output:
        with open(args.output, "w") as fh:
            json.dump(out, fh, indent=2)
            fh.write("\n")
    print("ALL PASSED" if ok else "SOME CHECKS FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
