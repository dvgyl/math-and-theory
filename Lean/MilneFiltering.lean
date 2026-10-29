module
public import MilneCore

@[expose] public section

open scoped BigOperators Matrix ComplexOrder
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace Milne

theorem onBob_one : onBob (1 : Matrix Q Q ℂ) = (1 : CMatrix) := by
  ext i j
  rcases i with ⟨i,a⟩
  rcases j with ⟨j,b⟩
  simp [onBob, Matrix.one_apply, Prod.mk_inj]
  split_ifs <;> simp_all

theorem onBob_mul (A B : Matrix Q Q ℂ) : onBob (A * B) = onBob A * onBob B := by
  ext i j
  rcases i with ⟨i,a⟩
  rcases j with ⟨j,b⟩
  fin_cases i <;> fin_cases j <;>
    simp [onBob, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two]

theorem onBob_conjTranspose (F : Matrix Q Q ℂ) :
    onBob Fᴴ = (onBob F)ᴴ := by
  ext i j
  simp only [onBob, Matrix.conjTranspose_apply]
  by_cases h : i.1 = j.1
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (Ne.symm h), star_zero]

theorem onBob_hermitian {F : Matrix Q Q ℂ} (hF : F.IsHermitian) :
    (onBob F).IsHermitian := by
  change (onBob F)ᴴ = onBob F
  rw [← onBob_conjTranspose, hF.eq]

/-- Bob's reduced matrix transforms by the same local congruence. -/
theorem partialB_filter (M : CMatrix) (F G : Matrix Q Q ℂ) :
    partialB (onBob F * M * onBob G) = F * partialB M * G := by
  ext i j
  simp [partialB, onBob, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two]
  ring

theorem pure_mulVec (H : CMatrix) (v : QQ → ℂ) :
    pure (H *ᵥ v) = H * pure v * Hᴴ := by
  ext i j
  simp [pure, Matrix.mul_apply, Matrix.mulVec, dotProduct,
    Matrix.conjTranspose_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
    star_add, StarMul.star_mul]
  ring

theorem filtered_ME_norm (F : Matrix Q Q ℂ) (hF : F.IsHermitian)
    (hTr : Matrix.trace (F * F) = 2)
    (v : QQ → ℂ) (hv : MaximallyEntangled v) :
    normSq (onBob F *ᵥ v) = 1 := by
  have hc : (normSq (onBob F *ᵥ v) : ℂ) = 1 := by
    rw [← pure_trace, ← trace_partialB, pure_mulVec, ← onBob_conjTranspose,
      partialB_filter, hv.2, hF.eq]
    simp only [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.trace_smul]
    rw [hTr]
    norm_num
  exact_mod_cast hc

theorem overlap_congruence (M H : CMatrix) (hH : H.IsHermitian) (v : QQ → ℂ) :
    overlap (H * M * H) v = overlap M (H *ᵥ v) := by
  unfold overlap
  rw [star_mulVec, hH.eq, ← dotProduct_mulVec, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec]

/-- The fully entangled-fraction bound in its arbitrary Bob-filter form, with no restriction on the
canonical state other than density and Bob marginal I/2. -/
theorem filtered_entangled_overlap_bound (M : CMatrix) (hM : Density M)
    (hB : partialB M = (1/2:ℂ) • (1 : Matrix Q Q ℂ))
    (F : Matrix Q Q ℂ) (hF : F.IsHermitian) (hTr : Matrix.trace (F * F) = 2)
    (v : QQ → ℂ) (hv : MaximallyEntangled v) :
    overlap (onBob F * M * onBob F) v ≤ 1 - center M / 2 := by
  have hp := canonical_operator_bound M hM hB
  have hn := filtered_ME_norm F hF hTr v hv
  have h := hp.re_dotProduct_nonneg (onBob F *ᵥ v)
  change 0 ≤ (dotProduct (star (onBob F *ᵥ v))
    ((((1-center M/2:ℝ):ℂ) • (1:CMatrix)-M) *ᵥ (onBob F *ᵥ v))).re at h
  rw [overlap_congruence M (onBob F) (onBob_hermitian hF) v]
  have hdot : (dotProduct (star (onBob F *ᵥ v)) (onBob F *ᵥ v)).re = 1 := by
    rw [← hn]
    simp only [dotProduct, normSq, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp [Complex.normSq_apply, Complex.mul_re, Complex.star_def]
  unfold overlap
  simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_sub, dotProduct_smul, smul_eq_mul, Complex.sub_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, hdot,
    mul_one] at h
  linarith

end Milne
