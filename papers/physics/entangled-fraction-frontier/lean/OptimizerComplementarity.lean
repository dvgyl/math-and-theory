import AllProofs
import Mathlib.LinearAlgebra.Matrix.Vec

/-!
# Actual optimizer complementarity for prescribed quantum marginals

This module closes the matrix-level bridge from optimal pure-target overlap
at prescribed marginals to complementary residual supports. It starts from
actual complex PSD matrices and the definitions checked in `AllProofs`.
No complementary-support conclusion is assumed.

The product of the two residual marginal matrices annihilates the target.
For a square target with invertible coefficient matrix, their ranks sum to
at most the local dimension, giving the sharp residual rank-product cap.
All dimensions are finite; the marginals may be singular.
-/
set_option autoImplicit false
noncomputable section
open Matrix
open scoped ComplexOrder Kronecker
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction
open MilneNew.RankOneExtraction
open MilneExpanded

namespace MilneContinuation

variable {a b : Type*} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]

abbrev residualA (A : Matrix a a ℂ) (w : a × b → ℂ) : Matrix a a ℂ :=
  A - partialTraceRight (outer w)

abbrev residualB (B : Matrix b b ℂ) (w : a × b → ℂ) : Matrix b b ℂ :=
  B - partialTraceLeft (outer w)

/-- Vanishing real expectation of a PSD matrix is exact kernel membership. -/
theorem expectation_zero_iff_mulVec_zero
    {R : Matrix (a × b) (a × b) ℂ} (hR : R.PosSemidef) (x : a × b → ℂ) :
    expectation R x = 0 ↔ R *ᵥ x = 0 := by
  rw [← hR.dotProduct_mulVec_zero_iff x]
  constructor
  · intro h
    rw [form_real hR x]
    change ((expectation R x : ℝ) : ℂ) = 0
    simp [h]
  · intro h
    exact congrArg Complex.re h

/-- Every coupling of the residual marginals completes the same feasible
vector to a coupling of the original marginals. -/
theorem residual_coupling_completion
    (A : Matrix a a ℂ) (B : Matrix b b ℂ) (w : a × b → ℂ)
    (R : Matrix (a × b) (a × b) ℂ)
    (hR : Compatible (residualA A w) (residualB B w) R) :
    Compatible A B (outer w + R) := by
  refine ⟨(outer_posSemidef w).add hR.1, ?_, ?_⟩
  · rw [partialTraceRight_add, hR.2.1]
    dsimp [residualA]
    abel
  · rw [partialTraceLeft_add, hR.2.2]
    dsimp [residualB]
    abel

/-- Every positive residual coupling of a reduced optimizer annihilates the
target. Thus all such completions are actual global state optimizers. -/
theorem every_residual_coupling_annihilates_target
    (A : Matrix a a ℂ) (B : Matrix b b ℂ)
    (hA : A.trace = 1) (hB : B.trace = 1) (x w : a × b → ℂ)
    (hopt : ∀ v, Admissible A B v → amplitude x v ≤ amplitude x w)
    (R : Matrix (a × b) (a × b) ℂ)
    (hR : Compatible (residualA A w) (residualB B w) R) :
    R *ᵥ x = 0 ∧
      expectation (outer w + R) x = (amplitude x w)^2 ∧
      ∀ N, Compatible A B N →
        expectation N x ≤ expectation (outer w + R) x := by
  have hM := residual_coupling_completion A B w R hR
  have hsub : (outer w + R - outer w).PosSemidef := by
    simpa only [add_sub_cancel_left] using hR.1
  have hz := optimizer_residual_expectation_zero A B hA hB x w hopt
    (outer w + R) hM hsub
  simp only [add_sub_cancel_left] at hz
  have hker := (expectation_zero_iff_mulVec_zero hR.1 x).mp hz
  have heq : expectation (outer w + R) x = (amplitude x w)^2 := by
    simp only [expectation, add_mulVec, dotProduct_add, Complex.add_re]
    change expectation (outer w) x + expectation R x = _
    rw [expectation_outer, hz, add_zero]
  refine ⟨hker, heq, ?_⟩
  intro N hN
  rw [heq]
  exact (fixed_marginal_bound_iff A B hA hB x (amplitude x w)
    (norm_nonneg _)).mpr hopt N hN

/-- The full product of residual marginal supports is orthogonal to the
target, proved from actual optimality and positivity. This includes zero
residual mass, without using any inverse at that boundary. -/
theorem optimizer_marginal_product_annihilates_target
    (A : Matrix a a ℂ) (B : Matrix b b ℂ)
    (hA : A.trace = 1) (hB : B.trace = 1) (x w : a × b → ℂ)
    (hw : Admissible A B w)
    (hopt : ∀ v, Admissible A B v → amplitude x v ≤ amplitude x w) :
    (residualA A w ⊗ₖ residualB B w) *ᵥ x = 0 := by
  let RA := residualA A w
  let RB := residualB B w
  have hpA : RA.PosSemidef := hw.1
  have hpB : RB.PosSemidef := hw.2
  have htr : RA.trace = RB.trace := by
    simp [RA, RB, residualA, residualB, trace_partialTraceRight,
      trace_partialTraceLeft, hA, hB]
  let δ : ℝ := RA.trace.re
  have hδ : 0 ≤ δ := (Complex.nonneg_iff.mp hpA.trace_nonneg).1
  have hRA : RA.trace = (δ : ℂ) := psd_trace_real hpA
  have hRB : RB.trace = (δ : ℂ) := htr.symm.trans hRA
  by_cases hz : δ = 0
  · have hzero : RA = 0 := hpA.trace_eq_zero_iff.mp (by simpa [hz] using hRA)
    change (RA ⊗ₖ RB) *ᵥ x = 0
    simp [hzero]
  · let R : Matrix (a × b) (a × b) ℂ := ((δ⁻¹ : ℝ) : ℂ) • (RA ⊗ₖ RB)
    have hpR : R.PosSemidef :=
      (hpA.kronecker hpB).smul (Complex.zero_le_real.mpr (inv_nonneg.mpr hδ))
    have hscale : ((δ⁻¹ : ℝ) : ℂ) * (δ : ℂ) = 1 := by
      norm_cast
      exact inv_mul_cancel₀ hz
    have hRight : partialTraceRight R = RA := by
      change partialTraceRight (((δ⁻¹ : ℝ) : ℂ) • Matrix.kronecker RA RB) = RA
      rw [partialTraceRight_smul, partialTraceRight_kronecker, hRB,
        smul_smul, hscale, one_smul]
    have hLeft : partialTraceLeft R = RB := by
      change partialTraceLeft (((δ⁻¹ : ℝ) : ℂ) • Matrix.kronecker RA RB) = RB
      rw [partialTraceLeft_smul, partialTraceLeft_kronecker, hRA,
        smul_smul, hscale, one_smul]
    have hker := (every_residual_coupling_annihilates_target
      A B hA hB x w hopt R ⟨hpR, hRight, hLeft⟩).1
    change (((δ⁻¹ : ℝ) : ℂ) • (RA ⊗ₖ RB)) *ᵥ x = 0 at hker
    rw [smul_mulVec] at hker
    have hc : ((δ⁻¹ : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast inv_ne_zero hz
    exact (smul_eq_zero.mp hker).resolve_left hc

/-- Row-major vectorization of the target coefficient matrix. -/
def targetVector (X : Matrix a b ℂ) (ij : a × b) : ℂ := X ij.1 ij.2

omit [DecidableEq a] [DecidableEq b] in
/-- Exact conversion of product-support annihilation to matrix multiplication.
The transpose on Bob's residual is required by row-major vectorization. -/
theorem marginal_product_annihilation_iff
    (A : Matrix a a ℂ) (B : Matrix b b ℂ) (X : Matrix a b ℂ) :
    (A ⊗ₖ B) *ᵥ targetVector X = 0 ↔ A * X * Bᵀ = 0 := by
  have heq : ∀ i j,
      ((A ⊗ₖ B) *ᵥ targetVector X) (i,j) = (A * X * Bᵀ) i j := by
    intro i j
    simp only [mulVec, dotProduct, kronecker_apply, targetVector,
      Fintype.sum_prod_type, mul_apply, transpose_apply, Finset.sum_mul]
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    ring
  constructor
  · intro h
    ext i j
    rw [← heq, h]
    rfl
  · intro h
    funext ij
    rw [heq, h]
    rfl

/-- End-to-end matrix complementarity, including arbitrary rectangular and
singular marginals. The zero product is a conclusion, not an assumption. -/
theorem optimizer_residual_matrix_complementarity
    (A : Matrix a a ℂ) (B : Matrix b b ℂ)
    (hA : A.trace = 1) (hB : B.trace = 1)
    (X : Matrix a b ℂ) (w : a × b → ℂ)
    (hw : Admissible A B w)
    (hopt : ∀ v, Admissible A B v →
      amplitude (targetVector X) v ≤ amplitude (targetVector X) w) :
    residualA A w * X * (residualB B w)ᵀ = 0 := by
  exact (marginal_product_annihilation_iff _ _ _).mp
    (optimizer_marginal_product_annihilates_target A B hA hB
      (targetVector X) w hw hopt)

omit [Fintype a] [DecidableEq a] [DecidableEq b] in
/-- Sylvester's rank inequality in a subtraction-free finite-matrix form. -/
theorem matrix_rank_sylvester {c : Type*} [Fintype c]
    (P : Matrix a b ℂ) (Q : Matrix b c ℂ) :
    P.rank + Q.rank ≤ (P * Q).rank + Fintype.card b := by
  let f := P.mulVecLin
  let g := Q.mulVecLin
  let L := LinearMap.range g
  let fL := f.domRestrict L
  let inclusion : LinearMap.ker fL →ₗ[ℂ] LinearMap.ker f :=
    { toFun := fun v => ⟨v.1.1, v.2⟩
      map_add' := by intro u v; rfl
      map_smul' := by intro z v; rfl }
  have hi : Function.Injective inclusion := by
    intro u v h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : LinearMap.ker f => z.1) h
  have hker : Module.finrank ℂ (LinearMap.ker fL) ≤
      Module.finrank ℂ (LinearMap.ker f) :=
    LinearMap.finrank_le_finrank_of_injective hi
  have hrange : LinearMap.range fL = LinearMap.range (f.comp g) := by
    dsimp [fL, L]
    rw [LinearMap.range_domRestrict, LinearMap.range_comp]
  have hsmall := LinearMap.finrank_range_add_finrank_ker fL
  have hlarge := LinearMap.finrank_range_add_finrank_ker f
  rw [hrange] at hsmall
  have hp : P.rank = Module.finrank ℂ (LinearMap.range f) := rfl
  have hq : Q.rank = Module.finrank ℂ L := rfl
  have hpq : (P * Q).rank = Module.finrank ℂ (LinearMap.range (f.comp g)) := by
    rw [Matrix.rank, Matrix.mulVecLin_mul]
  rw [hp, hq, hpq]
  rw [Module.finrank_fintype_fun_eq_card] at hlarge
  omega

/-- Rectangular target-sensitive rank complementarity: the target's actual
coefficient-matrix rank is its Schmidt rank. No nonsingularity is assumed. -/
theorem optimizer_rectangular_residual_rank_sum
    (A : Matrix a a ℂ) (B : Matrix b b ℂ)
    (hA : A.trace = 1) (hB : B.trace = 1)
    (X : Matrix a b ℂ) (w : a × b → ℂ)
    (hw : Admissible A B w)
    (hopt : ∀ v, Admissible A B v →
      amplitude (targetVector X) v ≤ amplitude (targetVector X) w) :
    (residualA A w).rank + (residualB B w).rank + X.rank ≤
      Fintype.card a + Fintype.card b := by
  have hz := optimizer_residual_matrix_complementarity A B hA hB X w hw hopt
  have hz' : residualA A w * (X * (residualB B w)ᵀ) = 0 := by
    simpa only [Matrix.mul_assoc] using hz
  have hleft := Matrix.rank_add_rank_le_card_of_mul_eq_zero hz'
  have hright := matrix_rank_sylvester X (residualB B w)ᵀ
  rw [Matrix.rank_transpose] at hright
  omega

/-- Actual full-Schmidt optimizer residuals have complementary total rank. -/
theorem optimizer_residual_rank_sum {d : ℕ}
    (A B X : Matrix (Fin d) (Fin d) ℂ)
    (hA : A.trace = 1) (hB : B.trace = 1) (hX : IsUnit X.det)
    (w : Fin d × Fin d → ℂ) (hw : Admissible A B w)
    (hopt : ∀ v, Admissible A B v →
      amplitude (targetVector X) v ≤ amplitude (targetVector X) w) :
    (residualA A w).rank + (residualB B w).rank ≤ d := by
  have hz := optimizer_residual_matrix_complementarity A B hA hB X w hw hopt
  have h := MilneExpanded.Structure.residual_rank_sum_le_dimension
    (residualA A w) (residualB B w)ᵀ X hX hz
  simpa only [Matrix.rank_transpose] using h

/-- The sharp rank-product cap derived from actual optimizer hypotheses. -/
theorem optimizer_residual_rank_product {d : ℕ}
    (A B X : Matrix (Fin d) (Fin d) ℂ)
    (hA : A.trace = 1) (hB : B.trace = 1) (hX : IsUnit X.det)
    (w : Fin d × Fin d → ℂ) (hw : Admissible A B w)
    (hopt : ∀ v, Admissible A B v →
      amplitude (targetVector X) v ≤ amplitude (targetVector X) w) :
    4 * ((residualA A w).rank * (residualB B w).rank) ≤ d^2 := by
  have hz := optimizer_residual_matrix_complementarity A B hA hB X w hw hopt
  have h := MilneExpanded.Structure.residual_product_rank_cap
    (residualA A w) (residualB B w)ᵀ X hX hz
  simpa only [Matrix.rank_transpose] using h

/-- Rank-one extraction with an explicit PSD residual, including the
zero-overlap boundary. -/
theorem compatible_extraction_with_positive_residual
    (A : Matrix a a ℂ) (B : Matrix b b ℂ)
    (M : Matrix (a × b) (a × b) ℂ) (hM : Compatible A B M)
    (x : a × b → ℂ) :
    ∃ w : a × b → ℂ,
      Admissible A B w ∧ (M - outer w).PosSemidef ∧
      expectation M x = (amplitude x w)^2 := by
  have ht : 0 ≤ expectation M x :=
    (Complex.nonneg_iff.mp (hM.1.dotProduct_mulVec_nonneg x)).1
  by_cases hpos : 0 < expectation M x
  · obtain ⟨w, hw, hov⟩ := normalized_extraction hM.1 x rfl hpos
    refine ⟨w, admissible_of_completion A B M w hM hw, hw, ?_⟩
    change star x ⬝ᵥ w = (Real.sqrt (expectation M x) : ℂ) at hov
    unfold amplitude
    rw [hov, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt ht]
  · have hz : expectation M x = 0 := by linarith
    have hzero : outer (0 : a × b → ℂ) = 0 := by
      ext i j
      simp [outer, vecMulVec]
    have hs : (M - outer (0 : a × b → ℂ)).PosSemidef := by
      simpa only [hzero, sub_zero] using hM.1
    refine ⟨0, admissible_of_completion A B M 0 hM hs, hs, ?_⟩
    simp [hz, amplitude]

/-- Every actual optimizer admits a positive residual decomposition with
unconditional target-sensitive support complementarity. This is the full
matrix bridge used in the written optimizer-rank theorem. -/
theorem actual_state_optimizer_residual_decomposition
    (A : Matrix a a ℂ) (B : Matrix b b ℂ)
    (hA : A.trace = 1) (hB : B.trace = 1) (X : Matrix a b ℂ)
    (M : Matrix (a × b) (a × b) ℂ) (hM : Compatible A B M)
    (hopt : ∀ N, Compatible A B N →
      expectation N (targetVector X) ≤ expectation M (targetVector X)) :
    ∃ (w : a × b → ℂ) (R : Matrix (a × b) (a × b) ℂ),
      M = outer w + R ∧ Admissible A B w ∧
      Compatible (residualA A w) (residualB B w) R ∧
      expectation M (targetVector X) = (amplitude (targetVector X) w)^2 ∧
      R *ᵥ targetVector X = 0 ∧
      residualA A w * X * (residualB B w)ᵀ = 0 ∧
      (residualA A w).rank + (residualB B w).rank + X.rank ≤
        Fintype.card a + Fintype.card b := by
  obtain ⟨w, hw, hs, heq⟩ := compatible_extraction_with_positive_residual
    A B M hM (targetVector X)
  have hwo : ∀ v, Admissible A B v →
      amplitude (targetVector X) v ≤ amplitude (targetVector X) w := by
    apply (fixed_marginal_bound_iff A B hA hB (targetVector X)
      (amplitude (targetVector X) w) (norm_nonneg _)).mp
    intro N hN
    rw [← heq]
    exact hopt N hN
  let R := M - outer w
  have hR : Compatible (residualA A w) (residualB B w) R := by
    refine ⟨hs, ?_, ?_⟩
    · change partialTraceRight (M - outer w) = _
      rw [partialTraceRight_sub, hM.2.1]
    · change partialTraceLeft (M - outer w) = _
      rw [partialTraceLeft_sub, hM.2.2]
  refine ⟨w, R, ?_, hw, hR, heq, ?_, ?_, ?_⟩
  · dsimp [R]
    abel
  · exact (every_residual_coupling_annihilates_target
      A B hA hB (targetVector X) w hwo R hR).1
  · exact optimizer_residual_matrix_complementarity A B hA hB X w hw hwo
  · exact optimizer_rectangular_residual_rank_sum A B hA hB X w hw hwo

/-- Every actual maximizing density matrix has a reduced maximizing vector
with the complementary residual-rank conclusions. -/
theorem actual_state_optimizer_has_complementary_residuals {d : ℕ}
    (A B X : Matrix (Fin d) (Fin d) ℂ)
    (hA : A.trace = 1) (hB : B.trace = 1) (hX : IsUnit X.det)
    (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hM : Compatible A B M)
    (hopt : ∀ N, Compatible A B N →
      expectation N (targetVector X) ≤ expectation M (targetVector X)) :
    ∃ w : Fin d × Fin d → ℂ,
      Admissible A B w ∧
      expectation M (targetVector X) = (amplitude (targetVector X) w)^2 ∧
      residualA A w * X * (residualB B w)ᵀ = 0 ∧
      (residualA A w).rank + (residualB B w).rank ≤ d ∧
      4 * ((residualA A w).rank * (residualB B w).rank) ≤ d^2 := by
  obtain ⟨w, hw, heq, hwo⟩ := state_optimizer_gives_reduced_optimizer
    A B hA hB M (targetVector X) hM hopt
  exact ⟨w, hw, heq,
    optimizer_residual_matrix_complementarity A B hA hB X w hw hwo,
    optimizer_residual_rank_sum A B X hA hB hX w hw hwo,
    optimizer_residual_rank_product A B X hA hB hX w hw hwo⟩

end MilneContinuation

#print axioms MilneContinuation.expectation_zero_iff_mulVec_zero
#print axioms MilneContinuation.every_residual_coupling_annihilates_target
#print axioms MilneContinuation.optimizer_marginal_product_annihilates_target
#print axioms MilneContinuation.marginal_product_annihilation_iff
#print axioms MilneContinuation.optimizer_residual_matrix_complementarity
#print axioms MilneContinuation.matrix_rank_sylvester
#print axioms MilneContinuation.optimizer_rectangular_residual_rank_sum
#print axioms MilneContinuation.optimizer_residual_rank_sum
#print axioms MilneContinuation.optimizer_residual_rank_product
#print axioms MilneContinuation.compatible_extraction_with_positive_residual
#print axioms MilneContinuation.actual_state_optimizer_residual_decomposition
#print axioms MilneContinuation.actual_state_optimizer_has_complementary_residuals
