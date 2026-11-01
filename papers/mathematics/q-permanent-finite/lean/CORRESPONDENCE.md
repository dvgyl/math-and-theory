# Manuscript to Lean correspondence

All declarations are in namespace `QPermanentResearch`; the frozen-input declarations are in `QPermanentResearch.Witness896`. The audit module `QPermanentResearch.AxiomAudit` checks every declaration of the 32 project modules, including private and generated ones, against the axioms `propext`, `Classical.choice` and `Quot.sound`. No proof uses `sorry`, an added axiom, `native_decide` or `Lean.ofReduceBool`.

## Definitions

| Manuscript | Lean |
|---|---|
| Inversion count of a permutation in the fixed coordinate order | `inversionCount` (Basic) |
| `P_q(A) = Σ_σ q^inv(σ) Π_i a_{i,σ(i)}` over a commutative semiring | `qPermanent` (Basic) |
| `D_q(A)`, the derivative in `q` | `qPermanentDerivative`, with `qPermanent_hasDerivAt` and `deriv_qPermanent` (Basic) |
| Fischer norm of the product polynomial `f = Π_i (v_i · z)` | `productFischerNorm` (WedgeNorm), from `colorCoefficient` and `colorWeight` (Fischer) |
| Fischer norm of the ordered wedge `G` | `wedgeFischerNorm`, from `wedgeCoefficient` and `rowWedge3` (WedgeNorm) |
| Four-row word of a type list, outermost type first | `d2Wrap` (D2Orbit), `d2Word`, `d2WordSize` (D2Compressed) |
| Integer type list and its real rows | `IntegerOrbit`, `integerOrbitReal` (IntegerD2) |
| Integer test `T_U > C(n,2) P` computed by the executable recurrence | `IntegerD2ThreeCertificate`, `integerD2ThreeDelta` (IntegerCertificate) |
| Rational matrices viewed as real matrices | `rationalMatrixCast` (RationalReduction) |
| `A ⊕ I_k` | `identityPadding` (IdentityPadding) |

## Results

| Manuscript | Lean |
|---|---|
| Lemma 2.1, `per B = ‖f‖²` for real Gram matrices of any rank | `gram_permanent_squares` (Fischer) |
| Lemma 2.1, `2D₁(VVᵀ) = C(n,2)‖f‖² − ‖G‖²` for real `n × 3` matrices `V` | `endpointDerivative_fischer`, `endpointDerivative_neg_iff_fischer` (WedgeNorm); the pair-minor form is `endpointDerivative_choose_pairMinorSum` (PairMinorIdentity) |
| Lemma 3.1, the four-row recurrences | `d2_factor_recurrence`, `d2_wedge01_recurrence`, `d2_wedge02_recurrence`, `d2_wedge12_recurrence` (D2Orbit); `d2Recurrence_represents` (D2Compressed) |
| Parity decomposition (3.8)–(3.10) | `d2_exact_endpoint`, `d2_negative_of_three_certificate` (D2Parity) |
| Executable integer recurrence and its semantics | `integerD2Recurrence_semantics` (IntegerD2), IntegerPolynomial, IntegerNorm |
| Certificate soundness for every type list | `integerD2ThreeCertificate_negative`, `integerD2ThreeCertificate_rational_counterexample` (IntegerCertificate) |
| Negative endpoint of a PSD matrix gives a rational PD matrix and rational `0 < q₁ < q₂ < 1` with `P_{q₂} < P_{q₁}` | `posSemidef_endpoint_to_rational_posDef_interior`, `gram_endpoint_to_rational_posDef_interior` (RationalReduction); real version `posSemidef_endpoint_to_posDef_interior` (EndpointReduction) |
| Identity padding preserves `P_q`, positive definiteness and rationality | `qPermanent_identityPadding`, `identityPadding_posDef`, `rational_posDef_decrease_identityPadding` (IdentityPadding) |
| Frozen input: rows, Gram matrix, order 896 | `Witness896.orbits`, `Witness896.rows`, `Witness896.gram`, `Witness896.row_count`, `Witness896.gram_posSemidef` |
| Frozen input: rank exactly three from rows 0, 1, 894 (determinant 480) | `Witness896.rankMinor_row_positions`, `Witness896.rankMinor_entries`, `Witness896.rankMinor_det`, `Witness896.rows_rank_three`, `Witness896.gram_rank_three` |
| Theorem 1.1 and the all-orders statement, from the Fischer-norm inequality for the frozen rows | `Witness896.gram_endpoint_negative_of_fischer`, `Witness896.all_large_dimensions_of_fischer` |
| The same, from the integer test for the frozen type list | `Witness896.gram_endpoint_negative_of_certificate`, `Witness896.all_large_dimensions_of_certificate` |
| From a negative endpoint of the frozen Gram matrix | `Witness896.rational_counterexample_of_endpoint`, `Witness896.all_large_dimensions_of_endpoint` |
| Scalar constants of Theorems 6.x (spherical families) | MeanFieldConstants, FourSphereConstants, FourSphereRefinement, JensenGap, PotentialGap, ComplexPotentialGap, ExplicitConstants |
| Finite matrix steps of the spectral obstruction | `posDef_add_lastCoordinateDiagonal`, `three_dimensional_principal_plane_lift_posDef` (PrincipalBlockLift); `matrix_eq_one_of_fix_nonsingular_columns` and companions (FixedPlaneGeometry) |

## Outside Lean

The hypotheses of the `Witness896.*_of_fischer` and `Witness896.*_of_certificate` theorems, that is, the finite integer comparison for the frozen input, are checked by the exact programs in [../certificate/](../certificate/), not in Lean. The explicit integer matrix `A = MB + I`, the explicit pair `q₁ = 1 − 2/Q`, `q₂ = 1 − 1/Q`, and the asymptotic, spectral, random-order and coherent-ordering theorems have conventional proofs in the manuscript.
