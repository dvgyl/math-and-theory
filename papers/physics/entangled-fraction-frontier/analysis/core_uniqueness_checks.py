"""Exact rational checks for the new unique-core theorem and its hypotheses.

These calculations test concrete examples; the quantified theorem is proved
in unique_reduced_optimizer.tex. SymPy arithmetic is exact throughout.
"""
from itertools import combinations
from pathlib import Path
import json
import sympy as s

Q = s.Rational


def outer(v):
    return v * v.conjugate().T


def partial_a(rho, m, n):
    return s.Matrix(m, m, lambda i, k: sum(rho[i*n+j, k*n+j] for j in range(n)))


def partial_b(rho, m, n):
    return s.Matrix(n, n, lambda j, l: sum(rho[i*n+j, i*n+l] for i in range(m)))


def psd_by_principal_minors(a):
    assert a == a.conjugate().T
    for k in range(1, a.rows + 1):
        for subset in combinations(range(a.rows), k):
            determinant = s.simplify(a.extract(subset, subset).det())
            assert determinant.is_nonnegative, (subset, determinant)


def admissible(w, a, b, m, n):
    psd_by_principal_minors(a - partial_a(outer(w), m, n))
    psd_by_principal_minors(b - partial_b(outer(w), m, n))


def overlap(x, rho):
    return s.simplify((x.conjugate().T * rho * x)[0])


results = {}

# Positive, noncommuting actual marginals, full-Schmidt target, and a nonzero
# cross block relative to the dual kernel. This catches an incorrect generic
# proof that sets the cross block itself to zero rather than comparing it.
x = s.Matrix([2, 0, 1, 2]) / 3
a = s.Matrix([[83, 8], [8, 17]]) / 100
b = s.Matrix([[17, 8], [8, 83]]) / 100
rho = s.Matrix([[16, 4, 4, 16], [4, 67, 1, 4],
                [4, 1, 1, 4], [16, 4, 4, 16]]) / 100
w = s.Matrix([4, 1, 1, 4]) / 10
z = s.Matrix([4, 0, 1, 4]) / 10
e = s.Matrix([0, 1, 0, 0])
h = s.diag(0, Q(17, 18))
k = s.diag(Q(17, 18), 0)
d = s.kronecker_product(h, s.eye(2)) + s.kronecker_product(s.eye(2), k)
slack = d - outer(x)
assert (x.T*x)[0] == 1
assert s.Matrix(2, 2, list(x)).det() != 0
assert a.det() > 0 and b.det() > 0 and a*b != b*a
assert partial_a(rho, 2, 2) == a and partial_b(rho, 2, 2) == b
assert rho.trace() == 1 and rho.rank() == 2
psd_by_principal_minors(rho)
psd_by_principal_minors(slack)
assert rho == outer(w) + Q(66, 100)*outer(e)
assert rho == outer(z) + z*(e/10).T + (e/10)*z.T + Q(67, 100)*outer(e)
assert overlap(x, rho) == Q(289, 900)
assert (h*a).trace() + (k*b).trace() == Q(289, 900)
assert rho*x / Q(17, 30) == w
assert slack*rho == s.zeros(4)
# All Hermitian operators supported on span{z,e} have four real parameters.
# Impose actual marginals, with no positivity assumption, and verify the
# unique solution. This gives an independent equality-case audit here.
c0, c1, cr, ci = s.symbols('c0 c1 cr ci', real=True)
general = c0*outer(z) + (cr+s.I*ci)*z*e.T + (cr-s.I*ci)*e*z.T + c1*outer(e)
equations = list(partial_a(general, 2, 2)-a) + list(partial_b(general, 2, 2)-b)
solution = s.solve(equations, (c0, c1, cr, ci), dict=True)
assert solution == [{c0: 1, c1: Q(67, 100), cr: Q(1, 10), ci: 0}]
results['noncommuting_positive_marginals'] = {
    'optimum': '289/900', 'state_rank': 2, 'dual_slack_rank': slack.rank(),
    'fixed_cross_amplitude': '1/10', 'coherent_core_squared_norm': str((w.T*w)[0]),
    'unique_state_from_exact_linear_kernel_equations': True,
    'exact_psd_certification': 'all principal minors nonnegative'
}

# Strict marginal positivity is necessary for uniqueness of the phase-fixed
# reduced vector, even when the target has full Schmidt rank.
a3 = s.diag(Q(1, 2), Q(1, 2), 0)
b3 = s.diag(Q(1, 2), 0, Q(1, 2))
x3 = s.zeros(9, 1)
for i in range(3):
    x3[3*i+i] = 1/s.sqrt(3)
w0 = s.zeros(9, 1); w0[0] = 1/s.sqrt(2)
w1 = w0.copy(); w1[5] = 1/s.sqrt(2)
for candidate in (w0, w1):
    admissible(candidate, a3, b3, 3, 3)
    assert s.simplify((x3.T*candidate)[0]) == 1/s.sqrt(6)
assert w0 != w1
results['singular_marginal_counterexample'] = {
    'dimension': 3, 'target_schmidt_rank': 3, 'two_distinct_reduced_maximizers': True,
    'optimal_overlap_squared': '1/6'
}

# Maximal target Schmidt rank is necessary even for positive marginals.
a2 = b2 = s.eye(2)/2
xp = s.Matrix([1, 0, 0, 0])
wp0 = s.Matrix([1, 0, 0, 0])/s.sqrt(2)
wp1 = s.Matrix([1, 0, 0, 1])/s.sqrt(2)
for candidate in (wp0, wp1):
    admissible(candidate, a2, b2, 2, 2)
    assert overlap(xp, outer(candidate)) == Q(1, 2)
results['product_target_counterexample'] = {
    'positive_marginals': True, 'target_schmidt_rank': 1,
    'two_distinct_reduced_maximizers': True, 'optimal_overlap_squared': '1/2'
}

# Isospectral marginals do not justify restricting to normalized pure couplings.
ai = s.diag(Q(7, 10), Q(3, 10))
bi = s.diag(Q(3, 10), Q(7, 10))
xi = s.Matrix([1, 0, 0, 1])/s.sqrt(2)
zi = s.sqrt(Q(3, 10))*s.Matrix([1, 0, 0, 1])
ri = outer(zi) + Q(2, 5)*outer(e)
assert partial_a(ri, 2, 2) == ai and partial_b(ri, 2, 2) == bi
assert overlap(xi, ri) == Q(3, 5)
theta = s.symbols('theta', real=True)
pure = s.Matrix([0, s.sqrt(Q(7, 10)), s.exp(s.I*theta)*s.sqrt(Q(3, 10)), 0])
assert overlap(xi, outer(pure)) == 0
assert partial_a(outer(pure), 2, 2) == ai
assert partial_b(outer(pure), 2, 2) == bi
results['pure_coupling_restriction_counterexample'] = {
    'positive_isospectral_marginals': True, 'all_pure_coupling_overlap': '0',
    'mixed_optimal_overlap': '3/5'
}

payload = {'method': 'SymPy exact rational and symbolic arithmetic',
           'all_assertions_passed': True, 'cases': results}
path = Path(__file__).with_name('core_uniqueness_check_results.json')
path.write_text(json.dumps(payload, indent=2)+'\n')
print(json.dumps(payload, indent=2))
