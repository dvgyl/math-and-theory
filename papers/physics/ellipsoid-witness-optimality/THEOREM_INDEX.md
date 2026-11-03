# Mathematics-to-Lean theorem index

This index maps the mathematical claims to declarations in the nine proof
modules in [lean/](lean/). Fully qualified names can be used directly with
`#check` and `#print axioms`. The fresh replay record in
[verification/replay/](verification/replay/) is the authoritative build record.
A source inventory is not, by itself, a compilation certificate.

**Verification for this release:** all nine modules, the aggregate `Main.lean`
and the whole-project audit `ProjectAxiomAudit.lean` were compiled with
`lake build Main ProjectAxiomAudit`. The audit covers every declaration defined
in the nine modules; every declaration other than Lean 4.19 code-generation
auxiliaries depends only on `propext`, `Classical.choice` and `Quot.sound`.
The script `AxiomAudit.lean` additionally prints the closures of 44 selected
theorems and the type signatures of five. The 207 explicit source declarations
counted below, the 44 selected closures and the number of environment
declarations in the whole-project audit are different counts.

The main distinction is between **concrete or parameterized theorems proved
without quantum-specific external hypotheses**, **general algebraic certificate
theorems**, and **structural assembly theorems with explicit hypotheses**. The
last category must not be described as an unconditional Lean formalization of
the complete arbitrary-target classification.

## 1. Exact declaration counts

Counts below are the explicit source declarations beginning with `lemma` or
`theorem`. Definitions, abbreviations, inductive constructors, generated
declarations, imported mathlib results, the Lake configuration, and the audit
script are excluded.

| Source module | Lemmas | Theorems | Total |
|---|---:|---:|---:|
| `EllipsoidCounterexample.lean` | 22 | 18 | 40 |
| `SameChirality.lean` | 5 | 13 | 18 |
| `ParametricFamily.lean` | 15 | 34 | 49 |
| `ClassCComparison.lean` | 15 | 24 | 39 |
| `NormalFormCertificates.lean` | 6 | 11 | 17 |
| `MirrorComparison.lean` | 0 | 6 | 6 |
| `GeometryCertificates.lean` | 0 | 16 | 16 |
| `ProductVector.lean` | 0 | 10 | 10 |
| `OptimalityReduction.lean` | 0 | 12 | 12 |
| **Total** | **63** | **144** | **207** |

These counts were checked against the final frozen sources. The 125 distinct
fully qualified declarations referenced by this index were also checked
against those sources; every reference resolves to a declared name. Final
compilation and axiom-audit evidence is recorded in
[verification/replay/](verification/replay/).

## 2. Definitions and conventions shared by the modules

| Mathematical object | Lean declaration | Exact meaning and scope |
|---|---|---|
| Complex two-qubit operator | `EllipsoidCounterexample.M4` | `Matrix (Fin 4) (Fin 4) ℂ`, in computational order `00,01,10,11`. |
| Complex two-qubit vector | `EllipsoidCounterexample.V4` | `Fin 4 → ℂ`. |
| Product vector | `EllipsoidCounterexample.product` | The actual four coefficients of `a ⊗ b`, for arbitrary complex two-vectors. |
| Hermiticity | `EllipsoidCounterexample.Hermitian` | Entrywise equality to the conjugate transpose. |
| Positive semidefiniteness | `EllipsoidCounterexample.PSD` | Hermiticity and nonnegative real quadratic form for every complex vector. |
| Density matrix | `EllipsoidCounterexample.State` | PSD and complex matrix trace equal to one. |
| Witness | `EllipsoidCounterexample.Witness` | Hermiticity, trace one, block positivity on all complex product vectors, and an explicit negative quadratic-form value for some vector. |
| Expectation | `EllipsoidCounterexample.expect` | The real part of `tr(Aρ)`. The concrete operators and states are certified Hermitian. |
| Fineness | `EllipsoidCounterexample.Finer` | `Finer V W` means every density matrix detected by `W` is detected by `V`. |
| Strict fineness | `EllipsoidCounterexample.StrictlyFiner` | Fineness plus a density matrix detected by `V` and not detected by `W`. Its equivalence to proper detection-set inclusion is proved in `OptimalityReduction.QuantumConnection.strictly_finer_iff`. |
| Bob partial transpose | `EllipsoidCounterexample.partialTranspose` | The computational-basis index swap defining partial transpose on the second qubit. |
| Actual Pauli data | `EllipsoidCounterexample.blochCoefficients` | Expectations against the explicitly defined Pauli tensor products. |
| Canonical frame | `EllipsoidCounterexample.Canonical` | All three Bob local Pauli coefficients vanish. |
| Canonical ellipsoid | `EllipsoidCounterexample.canonicalEllipsoid` | The image of the full real unit ball under the affine map read from the actual Pauli coefficients. Its steering interpretation requires canonicality, which is proved for the family. |
| Canonical containment problem | `EllipsoidCounterexample.InSet`, `EllipsoidCounterexample.OptimalIn` | These definitions explicitly restrict the surrounding set to canonical witnesses. |
| Optimality in an arbitrary set | `EllipsoidCounterexample.OptimalAmong` | No canonical restriction; the set is any set of complex `4×4` matrices. |

### Class C and Class D are represented consistently

There is **no standalone `ClassC` predicate** in these sources. Class C is
certified by the conjunction

```lean
EllipsoidCounterexample.Witness A ∧
  EllipsoidCounterexample.PSD (EllipsoidCounterexample.partialTranspose A)
```

The declaration `EllipsoidCounterexample.ClassD` includes witnesshood of both
`A` and its partial transpose, plus negative real determinants of both. Thus
Class D certificates do not rely solely on determinant signs.

The notation `M4` is reused in a separate namespace:
`GeometryCertificates.M4` is a **real** `4×4` matrix for an LMI. Its predicate
`GeometryCertificates.PSD4` is a symmetric real quadratic-form condition.
This is not an alias for the complex quantum-state type or PSD predicate.

`EllipsoidCounterexample.shapeMatrix` is `T Tᵀ` for the correlation block; it
is the physical shape matrix in the canonical frame. The noncanonical Class C
example is deliberately handled by its fractional map instead. The sources
do not apply this canonical shape formula to its noncanonical operator.

## 3. `EllipsoidCounterexample.lean`: the original rational certificate

The family is

\[
W_p=\tfrac12
\begin{pmatrix}p&0&0&0\\0&1-p&1&0\\0&1&1-p&0\\0&0&0&p\end{pmatrix}.
\]

| Mathematical statement | Fully qualified declaration |
|---|---|
| `W_p` is a witness for `0<p≤1`, with product positivity and an explicit negative vector | `EllipsoidCounterexample.W_witness` |
| The partial transpose is also a witness for `0<p<1` | `EllipsoidCounterexample.partialTranspose_witness` |
| Exact determinant formulas | `EllipsoidCounterexample.det_W`; `EllipsoidCounterexample.det_partialTranspose_W` |
| The rational pair `p=1/4,3/4` is Class D | `EllipsoidCounterexample.both_classD` |
| The actual Bloch matrix is `diag(1,1,1,2p−1)` | `EllipsoidCounterexample.W_blochCoefficients` |
| Canonicality of the family | `EllipsoidCounterexample.W_canonical` |
| The filled ellipsoids of `p` and `1−p` agree | `EllipsoidCounterexample.equal_ellipsoids` |
| Exact positive subtraction for the rational mirror pair | `EllipsoidCounterexample.exact_positive_subtraction` |
| Strict detection inclusion, with a rational separating state | `EllipsoidCounterexample.strict_fineness` |
| Admissibility, both Class D witnesses, equal ellipsoids, strict fineness and nonoptimality assembled | `EllipsoidCounterexample.counterexample` |
| The coarser witness is nonoptimal in **any** set containing the finer witness | `EllipsoidCounterexample.not_optimal_in_any_containing_set` |

**Scope.** This is an unconditional refutation of the sufficiency assertion
that every witness filling an admissible enclosure is optimal. The literal
necessary implication printed in Section IV.4 is a different assertion. The
counterexample does not refute that necessary implication. The last theorem
above transfers nonoptimality to arbitrary surrounding sets and avoids relying
on a canonical restriction on that surrounding set.

## 4. `SameChirality.lean`: refinement while the ellipsoid shrinks

This module uses `p=1/4` and `p=1/3`. Both are canonical Class D witnesses with
negative correlation determinant. The latter is strictly finer and has a
strictly smaller ellipsoid.

| Mathematical statement | Fully qualified declaration |
|---|---|
| Actual canonical correlation matrix and its determinant | `EllipsoidCounterexample.W_correlationMatrix`; `EllipsoidCounterexample.W_correlation_det` |
| Exact shape matrices for the original mirror pair | `EllipsoidCounterexample.exact_shape_matrices` |
| Both parameters in this comparison have negative chirality | `EllipsoidCounterexample.same_negative_chirality` |
| Exact PSD-subtraction identity for `1/4` versus `1/3` | `EllipsoidCounterexample.same_chirality_subtraction` |
| Strict fineness over all complex density matrices | `EllipsoidCounterexample.third_strict_fineness` |
| Proper containment of the finer witness's ellipsoid | `EllipsoidCounterexample.third_ellipsoid_proper` |
| The complete same-chirality certificate | `EllipsoidCounterexample.same_chirality_counterexample` |

**Scope.** Chirality is read from the actual correlation determinant only after
canonicality has been established. No generic claim that `det T` is the
chirality of an arbitrary noncanonical operator is used.

## 5. `ParametricFamily.lean`: exact order, geometry and quantitative separation

The following statements specialize naturally to `0<p,q≤1`, where the
operators are certified witnesses. Some source statements deliberately hold
over a larger parameter range; their exact hypotheses are explicit in Lean.

| Mathematical statement | Fully qualified declaration |
|---|---|
| A physical state `ρ_t` with expectation `(t−r)/2` against `W_r` | `EllipsoidCounterexample.boundaryState_state`; `EllipsoidCounterexample.boundaryState_expectation` |
| Division-free identity `qW_p=pW_q+(q−p)P_+` | `EllipsoidCounterexample.parametric_subtraction` |
| Complete fineness order: `W_q` finer than `W_p` iff `p≤q` | `EllipsoidCounterexample.parametric_finer_iff` |
| Complete strict order: strictly finer iff `p<q` | `EllipsoidCounterexample.parametric_strictlyFiner_iff` |
| Midpoint state gives expectations `±(q−p)/4` | `EllipsoidCounterexample.midpoint_separator` |
| Universal expectation-gap upper bound | `EllipsoidCounterexample.parametric_expectation_gap_bound` |
| No complex density matrix can achieve a larger common separation margin | `EllipsoidCounterexample.maximal_common_separation_margin` |
| `W_p−αW_q` is PSD iff `α=p/q` and `p≤q`, for `q>0` | `EllipsoidCounterexample.familyRemainder_psd_iff` |
| Ellipsoid containment iff `|2p−1|≤|2q−1|`, including the planar case | `EllipsoidCounterexample.parametric_ellipsoid_subset_iff` |
| Ellipsoid equality iff `p=q` or `p+q=1` | `EllipsoidCounterexample.parametric_ellipsoid_equal_iff` |
| The family ellipsoid lies in the Bloch ball and is admissible in the witness range | `EllipsoidCounterexample.parametric_ellipsoid_inside_ball`; `EllipsoidCounterexample.parametric_admissible` |
| Class D iff `0<p<1`, on `0≤p≤1` | `EllipsoidCounterexample.parametric_classD_iff` |
| Class C iff `p=1`, on `0≤p≤1` | `EllipsoidCounterexample.parametric_classC_iff` |
| An entire real interval of Class D mirror counterexamples | `EllipsoidCounterexample.infinite_ClassD_counterexamples` |
| Nonoptimality in any surrounding set containing the finer mirror | `EllipsoidCounterexample.parametric_not_optimal_in_any_containing_set` |
| Below `p=1/2`, increasing detection accompanies strictly shrinking geometry | `EllipsoidCounterexample.decreasing_geometry_increasing_detection` |
| Above `p=1/2`, increasing detection accompanies strictly expanding geometry | `EllipsoidCounterexample.increasing_geometry_increasing_detection` |
| Exact correspondence between the family parameter bound and geometric containment | `EllipsoidCounterexample.axialFamily_parameter_containment` |
| The unique optimizer within the displayed family under axial bound `r` is `W_((1+r)/2)` | `EllipsoidCounterexample.axialFamily_unique_optimal` |

**Scope.** The sharp margin bound quantifies over all complex density matrices,
not only Bell-diagonal states. In contrast, the last optimality theorem has an
explicitly restricted surrounding set, `EllipsoidCounterexample.axialFamily`.
It does not assert optimality against every arbitrary witness in that enclosure.
The analytic classification of all equality-margin states and pure-state
attainment in the notes is additional mathematics, not a theorem in this module.

## 6. `ClassCComparison.lean`: actual noncanonical Class C geometry

The module defines two concrete trace-one matrices `fine` and `coarse`. They
satisfy `coarse=(1/2)fine+(1/2)|00><00|`. Both are witnesses with PSD partial
transposes. The first has zero Bob Bloch vector; the second does not.

| Mathematical statement | Fully qualified declaration |
|---|---|
| Exact matrix subtraction identity and PSD product-state remainder | `EllipsoidCounterexample.ClassCComparison.positive_subtraction_identity`; `EllipsoidCounterexample.ClassCComparison.productProjector_psd` |
| Both matrices are actual Class C witnesses | `EllipsoidCounterexample.ClassCComparison.both_classC` |
| Strict detection improvement, with a physical rational separator | `EllipsoidCounterexample.ClassCComparison.fine_strictlyFiner` |
| Actual Pauli coefficients of both matrices | `EllipsoidCounterexample.ClassCComparison.fine_bloch`; `EllipsoidCounterexample.ClassCComparison.coarse_bloch` |
| Canonicality of the fine matrix and failure of canonicality for the coarse matrix | `EllipsoidCounterexample.ClassCComparison.fine_canonical`; `EllipsoidCounterexample.ClassCComparison.coarse_not_canonical` |
| Exact fractional steering maps computed from those Pauli coefficients | `EllipsoidCounterexample.ClassCComparison.fine_fractionalMap`; `EllipsoidCounterexample.ClassCComparison.coarse_fractionalMap` |
| Normalizing denominators are strictly positive on the full unit ball | `EllipsoidCounterexample.ClassCComparison.denominators_positive` |
| Noncontainment in both directions, using two exact points | `EllipsoidCounterexample.ClassCComparison.incomparable_ellipsoids` |
| The complete Class C example with strict refinement and incomparable ellipsoids | `EllipsoidCounterexample.ClassCComparison.classC_refinement_without_geometric_containment` |

**Scope.** Here `steeringEllipsoid` is the image of the actual **fractional**
Pauli map, not the canonical affine map. The comparison demonstrates that
global detection improvement need not imply either direction of geometric
containment, even in Class C. It does not violate relative optimality inside a
fixed enclosure: the finer matrix is outside the coarser enclosure. The
center/shape and volume calculations in the analytic note are not separately
named Lean theorems in this module.

## 7. `NormalFormCertificates.lean`: concrete matrix certificates in both forms

`EllipsoidNormalForms.bell w x y z` is the actual complex matrix
`w I+x XX+y YY+z ZZ`, with trace `4w`. The extraordinary matrix also retains
its nonunital parameter `k`; its trace is `4(w+k)`. These matrices are not
silently normalized to trace one.

| Mathematical statement | Fully qualified declaration |
|---|---|
| Explicit Bell-form sum-of-squares identity | `EllipsoidNormalForms.bell_quad` |
| PSD iff all four Bell linear expressions are nonnegative | `EllipsoidNormalForms.bell_psd_iff` |
| PSD is preserved by a nonnegative real scalar | `EllipsoidNormalForms.psd_real_smul` |
| Ordinary-form positive remainder | `EllipsoidNormalForms.ordinary_residual_psd` |
| Exact ordinary mirror subtraction identity | `EllipsoidNormalForms.ordinary_identity` |
| The ordinary subtraction difference is PSD | `EllipsoidNormalForms.ordinary_positive_certificate` |
| The ordinary witness coefficient lies strictly between zero and one | `EllipsoidNormalForms.ordinary_coefficient_bounds` |
| Extraordinary-form sum-of-squares remainder | `EllipsoidNormalForms.extraordinaryR_quad`; `EllipsoidNormalForms.extraordinary_residual_psd` |
| Exact extraordinary mirror subtraction and PSD difference | `EllipsoidNormalForms.extraordinary_identity`; `EllipsoidNormalForms.extraordinary_positive_certificate` |
| The extraordinary coefficient lies strictly between zero and one | `EllipsoidNormalForms.extraordinary_coefficient_bounds` |
| Exact positive sum-of-squares identity at the strict-interior example | `EllipsoidNormalForms.interior_remainder_quad` |

**Scope.** These are concrete complex-matrix algebra and PSD theorems under
stated real inequalities. The theorem placing an arbitrary block-positive
operator into the complete Lorentz normal forms is not formalized here. Nor
does this module by itself formalize pulling these inequalities through every
local filter, general trace-normalization, or the full mirror-dominance lemma.
The strict-interior identity supports the analytic robustness argument; it is
not a separately formalized theorem about an open neighborhood.

## 8. `MirrorComparison.lean`: every feasible mirror coefficient

Write

\[
B_\pm=I+aXX+bYY\pm cZZ,
\quad
1\ge a\ge b\ge c>0,
\quad a+b>1+c.
\]

The exact matrix feasibility interval is

\[
B_- - tB_+\succeq0
\iff
\frac{a+b-1-c}{a+b-1+c}\le t\le
\frac{1-a+b-c}{1-a+b+c}.
\]

| Mathematical statement | Fully qualified declaration |
|---|---|
| Explicit residual as another Bell-form matrix | `EllipsoidMirrorComparison.residual_identity` |
| The complete necessary-and-sufficient scalar interval | `EllipsoidMirrorComparison.sharp_mirror_interval` |
| Exact interval width `4c(1−a)/[(1−a+b+c)(a+b−1+c)]` | `EllipsoidMirrorComparison.mirror_interval_width` |
| Nonemptiness, including the `a=1` boundary | `EllipsoidMirrorComparison.mirror_interval_nonempty` |
| Strictly positive width for `a<1` | `EllipsoidMirrorComparison.mirror_interval_strict` |
| Feasibility of the coefficient used in the main proof | `EllipsoidMirrorComparison.minimum_coefficient_psd` |

**Scope.** The matrices have common trace four. The result concerns actual
complex PSD matrices, not only symbolic eigenvalue lists. Their interpretation
as a Class D mirror family and their ellipsoid geometry are supplied in the
manuscript, rather than additional predicates proved in this module.

## 9. `GeometryCertificates.lean`: containment LMI soundness and exact diagonal containment

The real matrix `rawCertificate` is the explicit `4×4` homogenized deficit
matrix. The target `metricEnclosure c H P` is defined by **both** the support
equation `P(x−c)=x−c` and the quadratic inequality `(x−c)ᵀH(x−c)≤1`.

| Mathematical statement | Fully qualified declaration |
|---|---|
| Cauchy-Schwarz mechanism in three real coordinates | `GeometryCertificates.lagrange_identity` |
| `‖b‖²<1` guarantees positive denominators on the closed unit ball | `GeometryCertificates.denominator_positive_of_marginal_bound` |
| Exact homogenization identity for the raw LMI | `GeometryCertificates.raw_certificate_identity` |
| PSD certificate plus nonnegative multiplier gives a nonnegative deficit | `GeometryCertificates.certificate_implies_deficit_nonnegative` |
| Fractional centering/deviation identity | `GeometryCertificates.fractional_deviation` |
| Raw LMI and support equations imply containment | `GeometryCertificates.raw_LMI_implies_containment` |
| The same implication using the directly checkable bound `‖b‖²<1` | `GeometryCertificates.raw_LMI_with_marginal_bound` |
| Canonical `b=0` specialization | `GeometryCertificates.canonical_LMI_implies_containment` |
| A concrete off-plane point satisfies the pseudoinverse quadratic inequality but fails the support equation | `GeometryCertificates.support_condition_is_essential` |
| Exact containment equivalence for centered aligned ellipsoids: containment iff every nonnegative semiaxis is at most its outer counterpart | `GeometryCertificates.diagonal_containment_iff` |

**Scope.** The general LMI statements prove **soundness**, not the converse
S-lemma implication. The identification of the enclosure with an arbitrary
ellipsoid via `H=Q⁺` and `P=QQ⁺` is explained mathematically in the manuscript; it
is not hidden inside the Lean hypotheses. The diagonal containment theorem is
a complete equivalence and explicitly covers zero semiaxes, disks, segments,
and points. It is a general geometric theorem, not a claim that low-dimensional
segments or points represent witnesses.

## 10. `ProductVector.lean`: the two-qubit product-vector theorem

Two-qubit vectors are identified with their actual `2×2` coefficient matrices,
using the same computational ordering as all quantum modules.

| Mathematical statement | Fully qualified declaration |
|---|---|
| Product vectors have zero coefficient determinant | `ProductVector.product_determinant_zero` |
| Zero determinant iff the vector factors as a tensor product | `ProductVector.determinant_zero_iff_product` |
| Exact quadratic determinant-pencil identity | `ProductVector.determinant_pencil` |
| Every complex quadratic with nonzero leading coefficient has a root | `ProductVector.complex_quadratic_has_root` |
| An independent pair spans a nonzero product vector, with coefficients and tensor factors returned | `ProductVector.independent_pair_contains_product` |
| Subspace version for a supplied independent pair | `ProductVector.subspace_with_independent_pair_contains_product` |
| Every complex two-qubit subspace of dimension at least two contains a nonzero product vector | `ProductVector.dimension_at_least_two_contains_product` |
| A subspace containing no nonzero product vector has dimension at most one | `ProductVector.completely_entangled_subspace_dimension_le_one` |

**Scope.** The algebraic closedness of the complex numbers is a proved mathlib
input, not a custom axiom asserting product-vector existence. The dimension
statement is connected to genuine `Module.finrank` and linear independence.
This proves an essential component of rank reduction. It does not itself prove
that subtracting the maximal product projector from an arbitrary PSD matrix
preserves PSD and lowers rank, or supply the pseudoinverse formula for that
subtraction.

## 11. `OptimalityReduction.lean`: explicit structural assembly

| Mathematical statement | Fully qualified declaration |
|---|---|
| In a faithful detection-set representation, a cofinal antichain is exactly the set of maximal detectors | `OptimalityReduction.classification_from_cofinal_antichain` |
| Without faithfulness, every optimal detection set is represented by a cofinal candidate | `OptimalityReduction.optimal_detection_set_is_candidate` |
| Abstract positive-remainder rank descent terminates at rank one | `OptimalityReduction.finite_rank_one_refinement` |
| A source of rank at most four requires at most three descent steps | `OptimalityReduction.rank_four_requires_at_most_three_steps` |
| Exact positive interpolation coefficients | `OptimalityReduction.interpolation_coefficients` |
| The corresponding refinement identity in any real module | `OptimalityReduction.interpolation_decomposition` |
| Exact displacement along the interpolation path | `OptimalityReduction.interpolation_difference` |
| Actual complex-matrix fineness equals inclusion of actual detected-state sets | `OptimalityReduction.QuantumConnection.finer_iff_subset` |
| The concrete strict-fineness definition equals proper inclusion | `OptimalityReduction.QuantumConnection.strictly_finer_iff` |
| The two concrete/abstract optimality definitions agree | `OptimalityReduction.QuantumConnection.optimalAmong_iff_detectionOptimal` |
| Matrix-specialized classification, **given explicit structural inputs** | `OptimalityReduction.QuantumConnection.quantum_classification_given_structural_inputs` |

**Scope of the classification theorem.** The matrix-specialized assembly still
requires: candidate membership in the surrounding set, cofinality, candidate
incomparability, and faithfulness of the normalized detection representation.
It does not prove these geometric/quantum inputs for arbitrary ellipsoids.
They are mathematical obligations in the manuscript, not omitted arguments
filled by a custom axiom or a `sorry`.

**Scope of rank descent.** The rank function and positive image map are
abstract. The theorem assumes a positive-remainder rank-drop step whenever the
rank is at least two. The product-vector theorem supplies a genuine part of
the intended quantum instantiation; the PSD rank-drop matrix calculation and
positive-map transport remain separate. The explicit step count is a proved
conclusion once those hypotheses are supplied.

**Scope of interpolation.** The module proves the coefficient signs and
algebraic decomposition. It does not silently supply closure of a particular
containment set, witness validity along the entire path, or chirality-continuity
arguments.

## 12. Dependency and coverage review

The source imports form the following small groups:

- `EllipsoidCounterexample` supplies the actual quantum matrix definitions.
  `SameChirality` extends it; `ParametricFamily` extends `SameChirality`; and
  `ClassCComparison` extends `ParametricFamily`.
- `NormalFormCertificates` uses the same complex quantum matrix definitions;
  `MirrorComparison` extends it.
- `GeometryCertificates`, `ProductVector`, and `OptimalityReduction` each
  import the base development and their additional mathlib dependencies.

The two partial-transpose class conventions, complex matrix order, unit-trace
state definition, and direction of fineness are consistent across the modules.
The real LMI matrices live in a distinct namespace. Noncanonical geometry is
handled explicitly. The abstract order assembly is connected to the concrete
detection definitions, but its quantum-specific hypotheses remain visible.

The following manuscript-level conclusions are **not** to be inferred merely from
the existence of these files or from a clean axiom audit: a fully instantiated
arbitrary-target classification; the general decomposability theorem; existence
of complete Lorentz normal forms; global Bob-orbit incomparability; the full
S-lemma equivalence and Moore-Penrose ellipsoid identification; optimizer
compactification; the strengthened polynomial witnesshood/optimality test; or
publication novelty. Their analytic arguments, external inputs, and literature
checks are documented separately. A theorem can have only standard axioms in
its closure while still having substantial **explicit hypotheses**; the tables
above track that distinction.
