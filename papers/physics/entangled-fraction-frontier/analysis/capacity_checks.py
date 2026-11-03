"""Exact arithmetic certificates for the uniform-marginal capacity results.

These checks use rational primal states and rational PSD decompositions of
dual slacks. No floating-point eigensolver or SDP solver is used.
"""
from pathlib import Path
import json
import sympy as sp


def basis(dim, index):
    v = sp.zeros(dim, 1)
    v[index] = 1
    return v


def partial_a(rho, n, m):
    return sp.Matrix(n, n, lambda i, k: sum(rho[i*m+j, k*m+j] for j in range(m)))


def partial_b(rho, n, m):
    return sp.Matrix(m, m, lambda j, l: sum(rho[i*m+j, i*m+l] for i in range(n)))


def zero(M):
    return all(sp.simplify(x) == 0 for x in M)


def capacity_case(n, m, weights):
    assert 1 <= n <= m and len(weights) == n and all(k >= 0 for k in weights)
    N = sum(k*k for k in weights)
    S = sum(weights)
    assert N > 0
    v = sum((basis(n*m, i*m+i) for i in range(n)), sp.zeros(n*m, 1))
    rho = v*v.T / m
    for i in range(n):
        for j in range(n, m):
            e = basis(n*m, i*m+j)
            rho += e*e.T / (n*m)
    x = sum((weights[i]*basis(n*m, i*m+i) for i in range(n)), sp.zeros(n*m, 1))
    target_projector = x*x.T/N
    K = sp.diag(*[sp.Rational(S*k, N) for k in weights], *([0]*(m-n)))
    D = sp.kronecker_product(sp.eye(n), K)

    # Exact decomposition of D-|x><x| into positive rank-one matrices.
    slack_certificate = sp.zeros(n*m)
    for i in range(n):
        for j in range(n):
            if i != j:
                e = basis(n*m, i*m+j)
                slack_certificate += K[j, j]*e*e.T
    for i in range(n):
        for j in range(i+1, n):
            e = basis(n*m, i*m+i)-basis(n*m, j*m+j)
            slack_certificate += sp.Rational(weights[i]*weights[j], N)*e*e.T

    predicted = sp.Rational(S*S, m*N)
    assert zero(D-target_projector-slack_certificate)
    assert zero(partial_a(rho, n, m)-sp.eye(n)/n)
    assert zero(partial_b(rho, n, m)-sp.eye(m)/m)
    assert sp.trace(rho) == 1
    assert sp.trace(rho*target_projector) == predicted
    assert sp.trace(K)/m == predicted
    assert sp.Rational(1, m) <= predicted <= sp.Rational(n, m)
    return {
        "dimensions": [n, m],
        "unnormalized_schmidt_amplitudes": weights,
        "capacity": str(predicted),
        "schmidt_rank": sum(k > 0 for k in weights),
        "projective_capacity": str(sp.Rational(sum(k > 0 for k in weights), m)),
        "rational_primal_and_dual_psd_certificates": "passed",
        "exact_marginals_trace_and_objective": "passed",
    }


cases = [
    capacity_case(2, 3, [1, 1]),
    capacity_case(2, 3, [1, 2]),
    capacity_case(2, 4, [1, 2]),
    capacity_case(3, 3, [1, 2, 3]),
    capacity_case(3, 4, [1, 2, 3]),
    capacity_case(3, 5, [1, 2, 3]),
    capacity_case(4, 4, [1, 2, 3, 4]),
    capacity_case(3, 3, [1, 1, 0]),
    capacity_case(3, 4, [2, 0, 0]),
]

# Standard three-dimensional antisymmetric state: exact support and marginals.
d = 3
swap = sp.zeros(d*d)
for i in range(d):
    for j in range(d):
        swap[i*d+j, j*d+i] = 1
Pminus = (sp.eye(d*d)-swap)/2
rho_minus = Pminus/3
psd_certificate = sp.zeros(d*d)
for i in range(d):
    for j in range(i+1, d):
        e = basis(d*d, i*d+j)-basis(d*d, j*d+i)
        psd_certificate += e*e.T/6
assert zero(Pminus*Pminus-Pminus)
assert zero(rho_minus-psd_certificate)
assert sp.trace(rho_minus) == 1
assert zero(partial_a(rho_minus, d, d)-sp.eye(d)/d)
assert zero(partial_b(rho_minus, d, d)-sp.eye(d)/d)
assert sp.trace(rho_minus*Pminus) == 1
a, b, c = sp.symbols("a b c", complex=True)
skew = sp.Matrix([[0, a, b], [-a, 0, c], [-b, -c, 0]])
assert sp.expand(skew.det()) == 0

result = {
    "arithmetic": "exact SymPy rational/symbolic arithmetic",
    "capacity_cases": cases,
    "printed_rectangular_statement_counterexample": {
        "dimensions": [2, 3],
        "maximally_entangled_target_capacity": "2/3",
        "printed_value": "1",
        "verification": "matching exact primal and positive rank-one dual decomposition",
    },
    "higher_dimensional_support_counterexample": {
        "dimensions": [3, 3],
        "state": "(I-swap)/6",
        "support_projection_capacity": "1",
        "both_marginals": "I_3/3",
        "every_support_coefficient_determinant": "0",
        "contains_maximally_entangled_vector": False,
        "exact_symbolic_certificates": "passed",
    },
}
out = Path(__file__).with_name("capacity_check_results.json")
out.write_text(json.dumps(result, indent=2)+"\n")
print(json.dumps(result, indent=2))
