"""Exact rational/radical certificates for the examples in theorem.tex.

All asserted identities and inequalities are checked by SymPy. Floating point
is used only to propose an ordering, followed by exact inequality assertions.
This script proves these instances, not the entire general theorem.
"""
import itertools
import json
from pathlib import Path
import sympy as S

Q = S.Rational
I = S.I
P = [S.eye(2), S.Matrix([[0, 1], [1, 0]]),
     S.Matrix([[0, -I], [I, 0]]), S.diag(1, -1)]


def zero(x):
    if isinstance(x, S.MatrixBase):
        assert all(S.simplify(v) == 0 for v in x), x
    else:
        assert S.simplify(x) == 0, x


def exact_max(values):
    winner = max(values, key=lambda v: float(S.N(v, 40)))
    for value in values:
        assert bool(S.simplify(winner - value) >= 0), (winner, value)
    return S.simplify(winner)


def positive_semidefinite(rho, strict=False):
    zero(rho - rho.conjugate().T)
    zero(S.trace(rho) - 1)
    for size in range(1, 5):
        for inds in itertools.combinations(range(4), size):
            minor = S.simplify(rho.extract(inds, inds).det())
            assert bool(minor > 0) if strict else bool(minor >= 0), (inds, minor)


def bloch(rho):
    R = S.Matrix(4, 4, lambda i, j:
                 S.simplify(S.trace(rho * S.kronecker_product(P[i], P[j]))))
    return R[1:, 0], R[0, 1:].T, R[1:, 1:]


def canonical(rho, side):
    a, b, T = bloch(rho)
    if side == "B":
        a, b, T = b, a, T.T
    alpha = S.sqrt(1 - a.dot(a))
    c = (b - T.T * a) / alpha**2
    D = ((alpha * S.eye(3) + a * a.T / (1 + alpha)) * T - a * b.T) / alpha**2
    return S.simplify(D), S.simplify(c)


def axis_optimum(D, c):
    zero(D - S.diag(*D.diagonal()))
    zero(c[:2, 0])
    A = D * D.T
    s = c.dot(c)
    d = D * c
    az = A[2, 2]
    transverse = exact_max([A[0, 0], A[1, 1]])
    boundary_values = [s + az + 2 * d[2], s + az - 2 * d[2]]
    curvature = az - transverse
    if curvature != 0:
        vertex = S.simplify(-d[2] / curvature)
        if bool(vertex >= -1) and bool(vertex <= 1):
            boundary_values.append(s + transverse + 2 * d[2] * vertex + curvature * vertex**2)
    E = exact_max(boundary_values)
    if s == 0:
        eigenvalues = list(A.diagonal())
        candidates = [S.trace(A) - x for x in eigenvalues]
    else:
        K = A - s * S.eye(3)
        assert K.det() != 0
        C = S.Matrix([[0, -d[2], 0], [d[2], 0, 0], [0, 0, 0]])
        M = S.simplify(A + C * K.inv() * C)
        zero(M - S.diag(*M.diagonal()))
        V = S.simplify(-K.inv() * C)
        zero(V.T * V - S.diag(*(V.T * V).diagonal()))
        eigenvalues = [S.simplify(x) for x in M.diagonal()]
        candidates = [S.simplify(S.trace(A) - eigenvalues[i]) for i in range(3)
                      if bool(S.simplify(V[:, i].dot(V[:, i])) <= 1)]
    value = exact_max([E] + candidates)
    return value, E, eigenvalues


def filtered(rho, F, side="A"):
    G = S.kronecker_product(F, P[0]) if side == "A" else S.kronecker_product(P[0], F)
    output = G * rho * G.conjugate().T
    probability = S.simplify(S.trace(output))
    return S.simplify(output / probability), probability


def main():
    results = {}
    rho1 = S.Matrix([[20, 0, 0, 14], [0, 0, 0, 0],
                     [0, 0, 7, 0], [14, 0, 0, 13]]) / 40
    positive_semidefinite(rho1)
    zero(rho1.det())
    assert rho1.rank() == 3
    a, b, T = bloch(rho1)
    zero(a)
    zero(b - S.Matrix([0, 0, Q(7, 20)]))
    zero(T - S.diag(Q(7, 10), -Q(7, 10), Q(13, 20)))
    value_a, boundary_a, eig_a = axis_optimum(*canonical(rho1, "A"))
    value_b, boundary_b, eig_b = axis_optimum(*canonical(rho1, "B"))
    zero(value_a - Q(79, 75)); zero(value_b - Q(292, 247))
    zero(boundary_a - 1)
    output, probability = filtered(rho1, S.diag(1, 2 / S.sqrt(17)))
    zero(probability - Q(21, 34))
    zero(bloch(output)[2] - S.diag(2*S.sqrt(17)/15, -2*S.sqrt(17)/15, Q(13, 15)))
    results["canonical_activation"] = {
        "rank": 3, "initial_B_squared": "49/50", "Alice_B_squared": str(value_a),
        "Bob_B_squared": str(value_b), "Alice_boundary_squared": str(boundary_a),
        "Alice_candidate_eigenvalues": list(map(str, eig_a)),
        "success_probability": str(probability)}

    rho2 = S.Matrix([[441, 0, 0, 56], [0, 49, 0, 0],
                     [0, 0, 1, 0], [56, 0, 0, 9]]) / 500
    positive_semidefinite(rho2, strict=True)
    a, b, T = bloch(rho2)
    zero(a - S.Matrix([0, 0, Q(24, 25)]))
    zero(b - S.Matrix([0, 0, Q(96, 125)]))
    zero(T - S.diag(Q(28, 125), -Q(28, 125), Q(4, 5)))
    zero(T[0, 0]**2 + T[2, 2]**2 - Q(10784, 15625))
    value_a, _, _ = axis_optimum(*canonical(rho2, "A"))
    Db, cb = canonical(rho2, "B")
    zero(cb - S.Matrix([0, 0, Q(5400, 6409)]))
    zero(Db - S.diag(28/S.sqrt(6409), -28/S.sqrt(6409), Q(980, 6409)))
    value_b, boundary_b, eig_b = axis_optimum(Db, cb)
    zero(value_a - Q(32, 25)); zero(value_b - Q(220, 221)**2)
    zero(value_b - boundary_b)
    Ab = Db * Db.T
    Kb = Ab - cb.dot(cb) * S.eye(3)
    assert all(bool(x < 0) for x in Kb.diagonal())
    assert bool(S.trace(Ab) < Q(27, 100))
    assert bool(boundary_b > S.trace(Ab))
    output, probability = filtered(rho2, S.diag(Q(1, 7), 1))
    zero(probability - Q(1, 25))
    zero(bloch(output)[2] - S.diag(Q(4, 5), -Q(4, 5), Q(4, 5)))
    bob_limit, bob_probability = filtered(rho2, S.diag(1, 0), "B")
    zero(bob_probability - Q(221, 250))
    zero(bloch(bob_limit)[0] - S.Matrix([0, 0, Q(220, 221)]))
    results["Alice_only_activation"] = {
        "rank": 4, "initial_B_squared": "10784/15625", "Alice_B_squared": str(value_a),
        "Bob_B_squared": str(value_b), "Alice_success_probability": str(probability),
        "Bob_rank_one_limit_probability": str(bob_probability),
        "Bob_invertible_maximum_exists": False}

    q = (15 - S.sqrt(105)) / 40
    D = S.diag(S.sqrt(Q(3, 10)), -Q(1, 2), S.sqrt(Q(1, 5)))
    c = S.Matrix([0, 0, S.sqrt(q)])
    R = S.zeros(4); R[0, 0] = 1; R[0, 1:] = c.T; R[1:, 1:] = D
    rho3 = sum((R[i, j] * S.kronecker_product(P[i], P[j])
                for i in range(4) for j in range(4)), S.zeros(4)) / 4
    positive_semidefinite(rho3, strict=True)
    value, boundary, eig = axis_optimum(D, c)
    zero(value - (15 + S.sqrt(105)) / 40)
    assert bool(S.simplify(value - boundary) > 0)
    assert sum(S.simplify(x-q) == 0 for x in eig) == 2
    results["exceptional_repeated_eigenvalue"] = {
        "s": str(q), "B_squared": str(value), "boundary_squared": str(boundary),
        "strictly_above_boundary": True, "candidate_eigenvalues": list(map(str, eig))}

    # Check the explicit pencil cubic, using symbolic diagonal K and arbitrary d.
    k1, k2, k3, x, y, z, t = S.symbols('k1 k2 k3 x y z t')
    K = S.diag(k1, k2, k3); d = S.Matrix([x, y, z])
    C = S.Matrix([[0, -z, y], [z, 0, -x], [-y, x, 0]])
    H = (K-t*S.eye(3)).row_join(-C).col_join(C.row_join(K))
    delta, qd = K.det(), (d.T*K*d)[0]
    e2 = k1*k2+k1*k3+k2*k3; r = d.dot(d)
    explicit = (-delta*t**3 + (delta*S.trace(K)+(d.T*K.adjugate()*d)[0]-e2*r)*t**2
                -(delta-qd)*(e2-r)*t+(delta-qd)**2)
    zero(S.expand(H.det(method='domain-ge') - explicit))
    results["explicit_cubic_identity"] = "symbolically_verified_for_diagonal_K_and_arbitrary_d"
    destination = Path(__file__).with_name('exact_results.json')
    destination.write_text(json.dumps(results, indent=2) + '\n')
    print(json.dumps(results, indent=2))
    print('PASS: all exact identities, inequalities, and positivity checks.')


if __name__ == '__main__':
    main()
