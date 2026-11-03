#!/usr/bin/env python3
"""Exact one-sided filtered F3 for rational two-qubit Bloch data.

All input, positivity checks, polynomials, root isolation, comparisons,
singular-pole tests, and value certificates use exact SymPy arithmetic.
The core never calls evalf, nroots, numerical eigensolvers, or optimizers.
For a generic sextic the output is an exact CRootOf expression, not radicals.

Public API:
    one_sided_exact(a, b, T, side='A') -> ExactF3Result
    both_sides_exact(a, b, T) -> {'A': result, 'B': result}
    validate_rational_bloch(a, b, T) -> RationalBlochState

Pass integers, fractions.Fraction, sympy.Rational, or exact rational strings.
Python/SymPy floating-point inputs are deliberately rejected.
"""
from __future__ import annotations

from dataclasses import dataclass
from itertools import combinations
import sympy as sp

Z = sp.Symbol('z')
Y = sp.Symbol('y')
I2 = sp.eye(2)
PAULI = (
    sp.Matrix([[0, 1], [1, 0]]),
    sp.Matrix([[0, -sp.I], [sp.I, 0]]),
    sp.Matrix([[1, 0], [0, -1]]),
)


def _rational(value):
    x = sp.sympify(value)
    if not isinstance(x, sp.Rational):
        raise TypeError('Bloch entries must be exact rational numbers; floats and irrational entries are rejected.')
    return x


def _vector(values):
    matrix = sp.Matrix(values)
    if matrix.shape == (1, 3):
        matrix = matrix.T
    if matrix.shape != (3, 1):
        raise ValueError('A Bloch vector must have exactly three entries.')
    return sp.ImmutableMatrix(matrix.applyfunc(_rational))


def _correlation(values):
    matrix = sp.Matrix(values)
    if matrix.shape != (3, 3):
        raise ValueError('The correlation matrix must have shape 3 by 3.')
    return sp.ImmutableMatrix(matrix.applyfunc(_rational))


def _scalar(matrix):
    return _rational(matrix[0])


def density_from_bloch(a, b, T):
    """Exact Hermitian density candidate, without asserting positivity."""
    a, b, T = _vector(a), _vector(b), _correlation(T)
    rho = sp.eye(4)
    for i in range(3):
        rho += a[i] * sp.kronecker_product(PAULI[i], I2)
        rho += b[i] * sp.kronecker_product(I2, PAULI[i])
        for j in range(3):
            rho += T[i, j] * sp.kronecker_product(PAULI[i], PAULI[j])
    return sp.ImmutableMatrix(rho / 4)


@dataclass(frozen=True)
class RationalBlochState:
    a: sp.ImmutableMatrix
    b: sp.ImmutableMatrix
    T: sp.ImmutableMatrix
    density: sp.ImmutableMatrix
    principal_minors: tuple

    def positivity_certificate(self):
        return [{'indices_zero_based': list(indices), 'determinant': str(value)}
                for indices, value in self.principal_minors]


def validate_rational_bloch(a, b, T):
    """Certify positivity by ALL 15 nonempty Hermitian principal minors.

    The Bloch construction already ensures Hermiticity and trace one;
    these are also checked exactly. No floating-point eigenvalue tolerance
    enters acceptance of a state.
    """
    a, b, T = _vector(a), _vector(b), _correlation(T)
    rho = density_from_bloch(a, b, T)
    if rho != rho.conjugate().T or sp.trace(rho) != 1:
        raise ArithmeticError('Exact Bloch reconstruction violated Hermiticity or trace one.')
    minors = []
    for size in range(1, 5):
        for indices in combinations(range(4), size):
            value = sp.expand(rho.extract(indices, indices).det(method='domain-ge'))
            value = _rational(value)
            minors.append((indices, value))
            if value < 0:
                raise ValueError(f'Not a physical density matrix: principal minor {indices} is {value}.')
    assert len(minors) == 15
    return RationalBlochState(a, b, T, rho, tuple(minors))


def _minpoly(expression):
    return sp.Poly(sp.minimal_polynomial(expression, Z), Z, domain=sp.QQ).monic()


def _poly_json(poly):
    return None if poly is None else str(poly.as_expr())


@dataclass
class ExactF3Result:
    side: str
    branch: str
    state: RationalBlochState
    value_squared: sp.Expr
    c: sp.ImmutableMatrix | None = None
    Q: sp.ImmutableMatrix | None = None
    invariants: dict | None = None
    D: sp.Poly | None = None
    N: sp.Poly | None = None
    P: sp.Poly | None = None
    nu: sp.Expr | None = None
    eta: sp.Expr | None = None
    nu_minpoly: sp.Poly | None = None
    eta_minpoly: sp.Poly | None = None
    derivative_order: int | None = None
    roots_strictly_above_d: int | None = None
    value_residue: sp.Poly | None = None
    certificates: dict | None = None
    attained_invertibly: bool | None = None

    @property
    def value(self):
        """The exact F3 value itself; value_squared is usually simpler."""
        return sp.sqrt(self.value_squared)

    def certifies_rational_value(self, expected):
        """Decide exact equality to a rational squared value by polynomial remainder."""
        expected = _rational(expected)
        if self.value_residue is None:
            return self.value_squared == expected
        return (self.value_residue-sp.Poly(expected, Z, domain=sp.QQ)).rem(self.eta_minpoly).is_zero

    def certifies_value_polynomial(self, polynomial):
        """Certify f(V)=0 in QQ[z]/minpoly(eta), never by RootOf.is_zero."""
        raw = sp.Poly(polynomial, Y)
        for coefficient in raw.all_coeffs():
            _rational(coefficient)
        f = sp.Poly(raw, Y, domain=sp.QQ)
        if self.value_residue is None:
            return f.eval(self.value_squared) == 0
        remainder = sp.Poly(0, Z, domain=sp.QQ)
        for coefficient in f.all_coeffs():
            remainder = (remainder*self.value_residue+
                         sp.Poly(coefficient, Z, domain=sp.QQ)).rem(self.eta_minpoly)
        return remainder.is_zero

    def value_minimal_polynomial(self):
        """Exact minimal polynomial of V by a resultant in its number field.

        The norm of y-V from the irreducible eta field is a power of V's
        minimal polynomial, so its rational factorization has one distinct
        irreducible factor. The returned polynomial is monic over QQ.
        """
        if self.value_residue is None:
            return sp.Poly(Y-self.value_squared, Y, domain=sp.QQ)
        resultant = sp.resultant(self.eta_minpoly.as_expr(),
                                Y-self.value_residue.as_expr(), Z)
        norm_polynomial = sp.Poly(resultant, Y, domain=sp.QQ)
        factors = sp.factor_list(norm_polynomial)[1]
        if len(factors) != 1:
            raise ArithmeticError('The algebraic value norm did not have a single irreducible factor.')
        minimal = factors[0][0].monic()
        if not self.certifies_value_polynomial(minimal.as_expr()):
            raise ArithmeticError('The resultant minimal polynomial failed the exact remainder certificate.')
        return minimal

    def to_dict(self, include_value_minpoly=False, include_principal_minors=True):
        result = {
            'side': self.side, 'branch': self.branch,
            'attained_by_an_invertible_filter': self.attained_invertibly,
            'squared_F3_exact': str(self.value_squared),
            'F3_exact': str(self.value),
            'canonical_c': None if self.c is None else [str(x) for x in self.c],
            'canonical_Q': None if self.Q is None else [[str(x) for x in row] for row in self.Q.tolist()],
            'six_invariants_and_d': None if self.invariants is None else
                {key: str(value) for key, value in self.invariants.items()},
            'D': _poly_json(self.D), 'N': _poly_json(self.N), 'P': _poly_json(self.P),
            'largest_real_root_nu': None if self.nu is None else str(self.nu),
            'eta': None if self.eta is None else str(self.eta),
            'nu_minimal_polynomial': _poly_json(self.nu_minpoly),
            'eta_minimal_polynomial': _poly_json(self.eta_minpoly),
            'derivative_order': self.derivative_order,
            'roots_strictly_above_rational_d': self.roots_strictly_above_d,
            'value_number_field_residue': _poly_json(self.value_residue),
            'certificates': self.certificates,
        }
        if include_principal_minors:
            result['density_principal_minors'] = self.state.positivity_certificate()
        if include_value_minpoly:
            result['squared_value_minimal_polynomial'] = str(self.value_minimal_polynomial().as_expr())
        return result


def _evaluate_validated(state, side):
    side = side.upper()
    if side == 'A':
        a, b, T = state.a, state.b, state.T
    elif side == 'B':
        a, b, T = state.b, state.a, state.T.T
    else:
        raise ValueError("side must be 'A' or 'B'.")
    delta = 1-_scalar(a.T*a)
    if delta < 0:
        raise ArithmeticError('Physical validation allowed an impossible marginal Bloch length.')
    if delta == 0:
        product_identity = T == a*b.T
        if not product_identity:
            raise ArithmeticError('A validated pure filtered marginal failed the exact product identity.')
        return ExactF3Result(side=side, branch='pure_filtered_marginal', state=state,
            value_squared=_scalar(b.T*b), attained_invertibly=True, certificates={
                'all_15_principal_minors_nonnegative': True,
                'exact_product_Bloch_identity_T_equals_a_bT': True,
                'pure_marginal_branch': True})

    B = T-a*b.T
    c = sp.ImmutableMatrix((b-T.T*a)/delta)
    Q = sp.ImmutableMatrix(B.T*(delta*sp.eye(3)+a*a.T)*B/delta**2)
    tau = _rational(sp.trace(Q))
    beta = _scalar(c.T*c)
    s2 = _rational((tau**2-sp.trace(Q*Q))/2)
    s3 = _rational(Q.det())
    u = _scalar(c.T*Q*c)
    v = _scalar(c.T*Q*Q*c)
    d = tau-beta
    D = sp.Poly(Z**3-tau*Z**2+s2*Z-s3, Z, domain=sp.QQ)
    N = sp.Poly(u*Z**2+(v-tau*u)*Z+s3*beta, Z, domain=sp.QQ)
    P = D**2+D*N.diff()-D.diff()*N
    if P.degree() != 6 or P.LC() != 1:
        raise ArithmeticError('The exact companion polynomial is not a monic sextic.')

    # real_roots uses exact rational isolation and returns ordered real
    # algebraic roots, including multiplicities. No factors are cancelled.
    roots = P.real_roots(radicals=False)
    if not roots:
        raise ArithmeticError('The physical companion unexpectedly has no real root.')
    nu = roots[-1]
    nu_minpoly = _minpoly(nu)
    if not P.rem(nu_minpoly).is_zero:
        raise ArithmeticError('The selected root failed its exact polynomial certificate.')

    # count_roots includes a rational endpoint and counts distinct roots.
    # Subtract its possible endpoint to compare nu with rational d exactly.
    strictly_above = int(P.count_roots(d, sp.oo))-int(P.eval(d) == 0)
    if strictly_above < 0:
        raise ArithmeticError('Inconsistent exact Sturm root count.')
    eta = nu if strictly_above else d
    eta_minpoly = _minpoly(eta)

    # The first derivative not divisible by minpoly(eta) detects the exact
    # multiplicity of eta in D. At compatible poles, N vanishes to at least
    # this same order. All tests are coefficient arithmetic over QQ.
    derivative_order = None
    D_r, N_r = D, N
    vanished_D, vanished_N = [], []
    for order in range(4):
        if not D_r.rem(eta_minpoly).is_zero:
            derivative_order = order
            break
        vanished_D.append(order)
        if not N_r.rem(eta_minpoly).is_zero:
            raise ArithmeticError('A selected physical pole is incompatible with the range condition.')
        vanished_N.append(order)
        D_r, N_r = D_r.diff(), N_r.diff()
    if derivative_order is None:
        raise ArithmeticError('A monic cubic cannot vanish through its third derivative.')

    numerator = sp.Poly(Z+beta, Z, domain=sp.QQ)*D_r+N_r
    denominator = D_r.rem(eta_minpoly)
    inverse_denominator = sp.invert(denominator, eta_minpoly)
    residue = (numerator*inverse_denominator).rem(eta_minpoly)
    if not (numerator-residue*D_r).rem(eta_minpoly).is_zero:
        raise ArithmeticError('Exact value reduction failed.')
    if residue.degree() <= 0:
        value_squared = residue.nth(0)
    else:
        # Preserve the compact requested derivative formula. Its equality
        # to residue(eta) is certified by the remainder test immediately above.
        value_squared = beta+eta+N_r.eval(eta)/D_r.eval(eta)
    branch = 'regular' if derivative_order == 0 else f'singular_pole_order_{derivative_order}'
    # eta=d is rational. In that branch the minimal-norm stationary effect
    # has radius squared -(N/D)'(eta), with all removable poles handled
    # by the next derivatives. Strict radius<1 is exactly GL attainment.
    stationary_radius_squared = None
    attained_invertibly = False
    if strictly_above == 0:
        stationary_radius_squared = _rational((N_r.eval(eta)*D_r.diff().eval(eta)-
            N_r.diff().eval(eta)*D_r.eval(eta))/
            ((derivative_order+1)*D_r.eval(eta)**2))
        if stationary_radius_squared < 0 or stationary_radius_squared > 1:
            raise ArithmeticError('An exact zero-multiplier radius certificate is outside the unit ball.')
        attained_invertibly = bool(stationary_radius_squared < 1)
    return ExactF3Result(side=side, branch=branch, state=state,
        value_squared=value_squared, c=c, Q=Q,
        invariants={'tau':tau,'beta':beta,'s2':s2,'s3':s3,'u':u,'v':v,'d':d},
        D=D,N=N,P=P,nu=nu,eta=eta,nu_minpoly=nu_minpoly,eta_minpoly=eta_minpoly,
        derivative_order=derivative_order,roots_strictly_above_d=strictly_above,
        value_residue=residue,attained_invertibly=attained_invertibly,certificates={
            'all_15_principal_minors_nonnegative': True,
            'nu_is_exact_largest_ordered_real_root': True,
            'P_remainder_mod_nu_minpoly_is_zero': True,
            'eta_comparison_method': 'Exact Sturm count of distinct roots strictly above rational d',
            'vanishing_D_derivative_orders': vanished_D,
            'vanishing_N_derivative_orders': vanished_N,
            'selected_D_derivative_nonzero_mod_eta_minpoly': True,
            'derivative_ratio_matches_value_residue_mod_eta_minpoly': True,
            'zero_multiplier_stationary_radius_squared':
                None if stationary_radius_squared is None else str(stationary_radius_squared),
            'no_floating_point_root_or_value_evaluation': True})


def one_sided_exact(a, b, T, side='A'):
    """Exact squared/value expression, certificates, and singular branch for one side."""
    return _evaluate_validated(validate_rational_bloch(a,b,T), side)


def both_sides_exact(a, b, T):
    """Both Equation 10 quantities, sharing one exact physical-state certificate."""
    state = validate_rational_bloch(a,b,T)
    return {side:_evaluate_validated(state, side) for side in ('A','B')}


if __name__ == '__main__':
    from pprint import pprint
    example=one_sided_exact([0,0,0],[0,0,sp.Rational(1,8)],
                           sp.diag(sp.Rational(3,4),-sp.Rational(3,4),sp.Rational(3,4)))
    pprint(example.to_dict(include_value_minpoly=True))
