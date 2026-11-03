GENUINELY EXACT RATIONAL-INPUT EVALUATOR
=======================================

Files
-----
exact_rational.py             Exact evaluator and public API.
verify_exact_rational.py      Exact certificates and additional decimal check.
exact_rational_results.json  Saved complete results, including all principal minors.

The implementation specializes the arbitrary-real analytical theorem to
rational Bloch input. Every physical acceptance decision, polynomial,
root selection, pole-order test, algebraic value, and equality certificate
is exact. The evaluator uses SymPy 1.14.0 and never invokes a numerical
root finder, floating eigenvalue solver, or filter optimizer. Generic
answers are rational functions of an exact CRootOf, as required by the
sextic Galois obstruction. This is a computational exact-arithmetic layer;
it does not extend the separately stated scope of Lean formalization.

Run
---
  python verify_exact_rational.py

This reruns 23 exact cases, covering both parties, derivative orders0--3,
pure and mixed marginals, singular joint states, a nonzero-gradient hard
case, rational violating values, noncanonical rational coordinates, and
the physical irreducible-sextic example. All exact assertions finish before
the optional final Float64 comparison is evaluated.

API examples
------------
  import sympy as sp
  from exact_rational import one_sided_exact, both_sides_exact

  R = sp.Rational
  result = one_sided_exact(
      [0, 0, 0],
      [0, 0, R(1, 8)],
      sp.diag(R(3, 4), -R(3, 4), R(3, 4)),
      side='A')

  assert result.value_squared == R(963, 568)
  assert result.certifies_rational_value(R(963, 568))
  assert result.attained_invertibly
  print(result.value)                 # sqrt(963/568), possibly simplified
  print(result.derivative_order)      # 0: ordinary ratio N(eta)/D(eta)
  print(result.value_minimal_polynomial())

  both = both_sides_exact(a, b, T)
  print(both['A'].value_squared, both['B'].value_squared)

Accepted entries are integers, fractions.Fraction, sympy.Rational, and
exact rational strings such as '1/8'. Python 1/8 evaluates to a float
before the API sees it and is deliberately rejected; use R(1,8) or '1/8'.
Irrational entries are outside this executable specialization, although
the mathematical theorem covers arbitrary real Bloch data.

The result exposes the exact c,Q, six scalar invariants, D,N,P, nu,eta,
minimal polynomials, singular derivative order, number-field residue of
the value, GL-attainment flag, and explicit certificates. The labels
'regular' and 'singular_pole_order_k' describe the algebraic pole only;
they do not by themselves describe whether the physical optimum is
attained by an invertible filter. Use attained_invertibly for that.

  result.to_dict(include_value_minpoly=True)

produces a JSON-compatible record. Exact expressions are represented by
strings so serialization introduces no rounding. The original validated
density matrix and its 15 exact principal minors remain available as
result.state.density and result.state.principal_minors.


Why the computation is exact
============================

1. Physicality is certified before evaluation.

The input determines the actual rational-complex Hermitian matrix

  rho=(I tensor I + sum a_i sigma_i tensor I
       +sum b_j I tensor sigma_j +sum T_ij sigma_i tensor sigma_j)/4.

Hermiticity and trace one are checked exactly. All 15 nonempty Hermitian
principal minors are computed as rational determinants and required to
be nonnegative. For Hermitian matrices, this is a necessary and sufficient
positive-semidefiniteness criterion; checking only the four leading minors
would not suffice. Accepted inputs therefore have an exact finite physical
certificate. Invalid input is rejected on the first negative minor.

2. Whitening introduces no irrational arithmetic into the invariants.

For Alice let delta=1-a.a and B=T-a*b^T. If delta>0 then

  c=(b-T^T*a)/delta,
  Q=B^T*(delta*I+a*a^T)*B/delta^2.

These are rational for every rational original Bloch state, even when
the matrix square root used to construct an actual whitening filter is
irrational. Define the six invariants

  tau=tr(Q), beta=c.c, s2=(tau^2-tr(Q^2))/2, s3=det(Q),
  u=c^T Q c, v=c^T Q^2 c,

and d=tau-beta. The exact polynomials are

  D(z)=z^3-tau*z^2+s2*z-s3,
  N(z)=u*z^2+(v-tau*u)*z+s3*beta,
  P(z)=D(z)^2+D(z)*N'(z)-D'(z)*N(z).

The checker independently verifies

  D(z)=det(zI-Q),
  N(z)=c^T Q adj(zI-Q)c,
  P(z)=det((zI-Q)^2-Q*c*c^T)

by rational matrix/polynomial arithmetic. No eigenbasis is computed.

3. Root selection and eta comparison are exact.

P.real_roots(radicals=False) returns the real algebraic roots in increasing
order, preserving multiplicity. The last entry is nu. No common factor is
cancelled from P: pole roots can encode genuine hard cases.

To decide eta=max(d,nu), the implementation counts distinct roots in the
closed interval [d,infinity] using exact Sturm arithmetic, and subtracts
one if P(d)=0. The result is the number of roots strictly above d. If it
vanishes, eta=d; otherwise eta=nu. Thus no decimal comparison, root
imaginary-part tolerance, or approximate equality at a pole is involved.

4. Singular poles use minimal-polynomial divisibility.

Let m be the monic minimal polynomial of eta over the rationals. A rational
polynomial f vanishes at eta if and only if f rem m is identically zero.
The implementation selects the first r in {0,1,2,3} for which

  D^(r) rem m != 0.

For every earlier derivative it verifies that N^(j) rem m=0 as well.
This is the exact range-compatibility check at a removable pole. It does
not rely on a symbolic expression's undecided .is_zero property after
substituting CRootOf. The answer is

  V=beta+eta+N^(r)(eta)/D^(r)(eta),   H_A=sqrt(V).

For r=0 this is the ordinary ratio. For r>0 it is the finite derivative
rule for the continuous extension of N/D. A monic cubic has nonzero third
derivative, so the four-case loop is complete. In particular Q=0 gives
D=z^3,N=0,eta=0,r=3; no divide-by-zero workaround is needed.

5. The returned value has an exact number-field certificate.

The numerator (beta+z)D^(r)+N^(r) and denominator D^(r) are reduced modulo
m. Since the denominator is nonzero modulo the irreducible m, it has a
polynomial inverse modulo m. Their product gives a polynomial R_V of
degree below deg(m) such that V=R_V(eta). The checker verifies

  [(beta+z)D^(r)+N^(r)-R_V*D^(r)] rem m = 0.

certifies_rational_value(q) checks R_V-q=0 in this quotient field.
certifies_value_polynomial(f) checks f(R_V) rem m=0. These are exact
coefficient identities, including for the generic sextic examples.

value_minimal_polynomial() computes the exact resultant

  Res_z(m(z), y-R_V(z)).

It is the field norm of y-V and therefore a power of the irreducible
minimal polynomial of V. Rational factorization extracts that one factor,
and an additional quotient-field calculation certifies that it annihilates
the returned value. The generic physical example has degree six for both
eta and V; its RootOf representation is therefore substantive, not a
rational value hidden behind unnecessary notation.

6. The pure-marginal branch and both filtering directions are explicit.

If delta=0, all arithmetic remains rational and the implementation checks
the product identity T=a*b^T forced by positivity. It returns V=b.b and
records that every invertible filter on that side is optimal. Bob is
handled by the exact substitution (a,b,T)->(b,a,T^T), reusing the original
physical-state certificate. There is no numerical purity tolerance.

7. Invertible attainment is also decided exactly.

If eta>d, the positive trust-region multiplier forces all maximizers onto
the rank-one boundary, so no GL filter attains the value. If eta=d, eta is
rational and the squared radius of the minimal-norm stationary effect is

  R0=[N^(r) D^(r+1)-N^(r+1) D^(r)] /
     [(r+1)(D^(r))^2], evaluated at eta.

This is -(N/D)' at the removable pole. All terms are rational in this
branch. The exact GL-attainment condition is R0<1. The code verifies
0<=R0<=1 and returns the corresponding Boolean. This correctly separates
the full-rank product example, singular flat maxima, and interior violating
optima.


Representative exact results
============================
Werner with T=-pI:             V_A=V_B=3p^2.
Product, Q=0, b_z=3/5:         V_A=9/25, r=3, no invertible maximizer.
Flat S=diag(0,0,1/2):          V_A=1/4, r=1, invertible maximizers exist.
Double-pole flat example:      V_A=2/25, r=2.
Nonzero-gradient hard case:    V_A=36/275, r=1, no invertible maximizer.
Rational violating example:    V_A=963/568, r=0, invertible maximum.
Pure entangled rational state: V_A=V_B=3.

For the physical Galois example

  a=0, c=(1/5,1/6,1/7), S=diag(1/20,1/15,1/10),

nu is exactly CRootOf(P0,1), where

  P0(z)=3175200000000000*z^6-107604000000000*z^5
       +65685000000*z^4+18599100000*z^3-188411500*z^2+695840*z-913.

Here eta=nu and r=0. The exact returned V is beta+nu+N(nu)/D(nu), with

  beta=3889/44100,
  D=z^3-(61/3600)z^2+(29/360000)z-1/9000000,
  N=(16969/39690000)z^2-(17483/3969000000)z+3889/396900000000.

The primitive sextic agrees with the independent finite-field Galois
certificate. A rational Bob rotation yields the same invariant polynomial
and the same quotient-field value residue, checked exactly. A generic
rational full-rank density example additionally tests both directions with
nontrivial rational original-coordinate whitening invariants.

All 23 exact checks passed. The separate decimal comparison with the
existing Float64 evaluator differs by at most 1.12e-16. This last number
is reported only as a consistency check; it is not used to establish any
exact equality, physicality, branch selection, or global optimum.

Official implementation reference
==================================
SymPy1.14 polynomial reference documents exact real_roots, its increasing
root ordering, radicals=False, polynomial remainders and interval root
counts:
https://docs.sympy.org/latest/modules/polys/reference.html

The analytical global-optimality proof is in manuscript.tex and its sections;
the exact-arithmetic program evaluates that proven closed form. Its
rational-input scope should not be confused with a restriction on the
arbitrary-real mathematical theorem or with an additional Lean proof.
