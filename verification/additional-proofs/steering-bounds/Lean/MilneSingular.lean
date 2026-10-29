import MilneFiltering
import MilneQubit
import MilnePurityCovariance
import Mathlib.Tactic.LinearCombination

open scoped BigOperators Matrix ComplexOrder
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace Milne

/-- A positive matrix with zero trace vanishes. -/
theorem psd_eq_zero_of_trace_zero {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.PosSemidef) (htr : Matrix.trace A = 0) : A = 0 := by
  have hs : ∑ i, hA.1.eigenvalues i = 0 := by
    rw [← trace_eq_eigenvalue_sum hA.1, htr]
    simp
  have hef : hA.1.eigenvalues = 0 :=
    (Fintype.sum_eq_zero_iff_of_nonneg hA.eigenvalues_nonneg).mp hs
  have he : ∀ i, hA.1.eigenvalues i = 0 := fun i => congrFun hef i
  rw [hA.1.spectral_theorem]
  have hd : Matrix.diagonal (RCLike.ofReal ∘ hA.1.eigenvalues) =
      (0 : Matrix n n ℂ) := by
    ext i j
    simp [Matrix.diagonal_apply, Function.comp_def, he]
  rw [hd, mul_zero, zero_mul]

/-- A zero positive congruence forces its columns into the kernel. -/
theorem psd_mul_eq_zero_of_congruence {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.PosSemidef) (D : Matrix n n ℂ)
    (hzero : Dᴴ * A * D = 0) : A * D = 0 := by
  have hz : Dᴴ * (A * D) = 0 := by simpa only [Matrix.mul_assoc] using hzero
  ext i j
  have hquad : dotProduct (star (fun k => D k j)) (A *ᵥ (fun k => D k j)) = 0 := by
    have h := congrArg (fun X : Matrix n n ℂ => X j j) hz
    simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.mulVec,
      dotProduct, Pi.star_apply, Matrix.zero_apply] using h
  have hk := (hA.dotProduct_mulVec_zero_iff (fun k => D k j)).mp hquad
  have hi := congrFun hk i
  simpa only [Matrix.mul_apply, Matrix.mulVec, dotProduct, Pi.zero_apply,
    Matrix.zero_apply] using hi

/-- The two-dimensional Cayley--Hamilton identity at trace one and determinant zero. -/
theorem qubit_idempotent_of_trace_one_det_zero (B : Matrix Q Q ℂ)
    (htr : Matrix.trace B = 1) (hdet : B.det = 0) : B * B = B := by
  have ht : B 0 0 + B 1 1 = 1 := by
    simpa only [Matrix.trace, Matrix.diag, Fin.sum_univ_two] using htr
  have hd : B 0 0 * B 1 1 - B 0 1 * B 1 0 = 0 := by
    simpa only [Matrix.det_fin_two] using hdet
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [Matrix.mul_apply, Fin.sum_univ_two]
  · change B 0 0 * B 0 0 + B 0 1 * B 1 0 = B 0 0
    linear_combination (B 0 0) * ht - hd
  · change B 0 0 * B 0 1 + B 0 1 * B 1 1 = B 0 1
    linear_combination (B 0 1) * ht
  · change B 1 0 * B 0 0 + B 1 1 * B 1 0 = B 1 0
    linear_combination (B 1 0) * ht
  · change B 1 0 * B 0 1 + B 1 1 * B 1 1 = B 1 1
    linear_combination (B 1 1) * ht - hd

theorem onBob_sub_boundary (A B : Matrix Q Q ℂ) :
    onBob (A-B) = onBob A - onBob B := by
  ext i j
  by_cases h : i.1 = j.1 <;> simp [onBob, h]

/-- A density matrix with a singular Bob marginal is supported on that
rank-one marginal. The statement concerns the actual complex density matrix. -/
theorem singular_Bob_support (M : CMatrix) (hM : Density M)
    (hdet : (partialB M).det = 0) :
    M = onBob (partialB M) * M * onBob (partialB M) := by
  let B := partialB M
  have hB : B.PosSemidef := partialB_psd hM.1
  have htrB : Matrix.trace B = 1 := by
    dsimp [B]
    rw [trace_partialB, hM.2]
  have hBB : B * B = B := qubit_idempotent_of_trace_one_det_zero B htrB hdet
  let K := onBob (1-B)
  have hK : K.IsHermitian :=
    onBob_hermitian (Matrix.isHermitian_one.sub hB.1)
  have hR : (K * M * K).PosSemidef := by
    simpa only [hK.eq] using hM.1.mul_mul_conjTranspose_same K
  have hsmall : (1-B)*B*(1-B) = 0 := by
    rw [sub_mul, one_mul, hBB, sub_self, zero_mul]
  have htrR : Matrix.trace (K*M*K) = 0 := by
    rw [← trace_partialB]
    dsimp [K]
    rw [partialB_filter]
    change Matrix.trace ((1-B)*B*(1-B)) = 0
    rw [hsmall]
    simp
  have hRzero : K*M*K = 0 := psd_eq_zero_of_trace_zero hR htrR
  have hMK : M*K = 0 := psd_mul_eq_zero_of_congruence hM.1 K (by
    simpa only [hK.eq] using hRzero)
  have hKM : K*M = 0 := by
    have hh := congrArg Matrix.conjTranspose hMK
    simpa only [Matrix.conjTranspose_mul, hK.eq, hM.1.1.eq,
      Matrix.conjTranspose_zero] using hh
  have hcomp : 1-K = onBob B := by
    dsimp [K]
    rw [onBob_sub_boundary, onBob_one]
    abel
  calc
    M = (1-K)*M*(1-K) := by
      rw [sub_mul, one_mul, hKM, sub_zero, mul_sub, mul_one, hMK, sub_zero]
    _ = onBob (partialB M) * M * onBob (partialB M) := by rw [hcomp]

/-- Every density matrix is bounded above by the identity operator. -/
theorem density_le_identity (M : CMatrix) (hM : Density M) :
    ((1 : CMatrix)-M).PosSemidef := by
  have hs : ∑ i, hM.1.1.eigenvalues i = 1 := by
    rw [← trace_eq_eigenvalue_sum hM.1.1, hM.2]
    rfl
  have he : ∀ i, hM.1.1.eigenvalues i ≤ 1 := by
    intro i
    calc
      hM.1.1.eigenvalues i ≤ ∑ j, hM.1.1.eigenvalues j :=
        Finset.single_le_sum (fun j _ => hM.1.eigenvalues_nonneg j) (Finset.mem_univ i)
      _ = 1 := hs
  let U : CMatrix := hM.1.1.eigenvectorUnitary
  have hd : (Matrix.diagonal (fun i => ((1-hM.1.1.eigenvalues i : ℝ):ℂ))).PosSemidef := by
    apply Matrix.posSemidef_diagonal_iff.mpr
    intro i
    have hi : 0 ≤ 1-hM.1.1.eigenvalues i := sub_nonneg.mpr (he i)
    exact RCLike.ofReal_nonneg.mpr hi
  have hds : Matrix.diagonal (fun i => ((1-hM.1.1.eigenvalues i : ℝ):ℂ)) =
      (1 : CMatrix) - Matrix.diagonal (RCLike.ofReal ∘ hM.1.1.eigenvalues) := by
    ext i j
    by_cases hij : i = j <;> simp [hij, Matrix.diagonal_apply, Matrix.one_apply]
  have h := hd.mul_mul_conjTranspose_same U
  rw [hds, mul_sub, sub_mul, mul_one] at h
  have hu : U * Uᴴ = (1 : CMatrix) := by
    simp [U, ← Matrix.star_eq_conjTranspose]
  have hspec : U * Matrix.diagonal (RCLike.ofReal ∘ hM.1.1.eigenvalues) * Uᴴ = M := by
    simpa [U, ← Matrix.star_eq_conjTranspose] using hM.1.1.spectral_theorem.symm
  rw [hu, hspec] at h
  exact h

/-- A density-matrix expectation cannot exceed the squared vector norm. -/
theorem density_overlap_le_normSq (M : CMatrix) (hM : Density M) (v : QQ → ℂ) :
    overlap M v ≤ normSq v := by
  have h := (density_le_identity M hM).re_dotProduct_nonneg v
  change 0 ≤ (dotProduct (star v) (((1 : CMatrix)-M) *ᵥ v)).re at h
  have hv : (dotProduct (star v) v).re = normSq v := by
    simp only [dotProduct, normSq, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp [Complex.normSq_apply, Complex.mul_re, Complex.star_def]
  unfold overlap
  simp only [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub,
    Complex.sub_re, hv] at h
  linarith

/-- Projecting a maximally entangled vector onto a pure Bob state has
squared norm one half. -/
theorem pure_Bob_ME_projected_norm (B : Matrix Q Q ℂ) (hB : B.IsHermitian)
    (hBB : B*B = B) (htrB : Matrix.trace B = 1)
    (v : QQ → ℂ) (hv : MaximallyEntangled v) :
    normSq (onBob B *ᵥ v) = 1/2 := by
  have hc : (normSq (onBob B *ᵥ v) : ℂ) = (1/2:ℂ) := by
    rw [← pure_trace, ← trace_partialB, pure_mulVec, ← onBob_conjTranspose,
      partialB_filter, hv.2, hB.eq]
    simp only [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.trace_smul]
    rw [hBB, htrB]
    simp [smul_eq_mul]
  have hh := congrArg Complex.re hc
  norm_num at hh
  exact hh

/-- The genuine fully-entangled-fraction boundary estimate when Bob's
marginal is singular. It holds for every maximally entangled vector. -/
theorem singular_Bob_entangled_overlap_bound (M : CMatrix) (hM : Density M)
    (hdet : (partialB M).det = 0) (v : QQ → ℂ) (hv : MaximallyEntangled v) :
    overlap M v ≤ 1/2 := by
  have hB := partialB_psd hM.1
  have htrB : Matrix.trace (partialB M) = 1 := by rw [trace_partialB, hM.2]
  have hBB := qubit_idempotent_of_trace_one_det_zero (partialB M) htrB hdet
  calc
    overlap M v = overlap M (onBob (partialB M) *ᵥ v) := by
      conv_lhs => rw [singular_Bob_support M hM hdet]
      exact overlap_congruence M (onBob (partialB M)) (onBob_hermitian hB.1) v
    _ ≤ normSq (onBob (partialB M) *ᵥ v) := density_overlap_le_normSq M hM _
    _ = 1/2 := pure_Bob_ME_projected_norm (partialB M) hB.1 hBB htrB v hv


/-- A singular trace-one Bob marginal has unit Bloch length. -/
theorem singular_Bob_blochSq (M : CMatrix) (hM : Density M)
    (hdet : (partialB M).det = 0) : blochSq (partialB M) = 1 := by
  rw [blochSq_det_identity (partialB_psd hM.1).1, trace_partialB, hM.2, hdet]
  norm_num

/-- Singular Bob support annihilates the conditional collision-purity
polynomial, using its exact determinant covariance. -/
theorem singular_Bob_purityDifference_zero (M : CMatrix) (hM : Density M)
    (hdet : (partialB M).det = 0) : purityDifference M = 0 := by
  have h := purityDifference_filter M (partialB M)
  rw [← singular_Bob_support M hM hdet, hdet] at h
  simpa using h

end Milne
