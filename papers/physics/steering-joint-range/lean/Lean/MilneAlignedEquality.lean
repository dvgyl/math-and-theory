import MilneAlignedState

open scoped BigOperators Matrix ComplexOrder
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 24000000
set_option maxRecDepth 16000
noncomputable section
namespace Milne

theorem aligned_product_00_10 (c t : ℝ) (z w v : ℂ) :
    (alignedState c t z w v * geometryFlip geometryEz (alignedState c t z w v))
      (0,0) (1,0) = -(t:ℂ)*z/2 := by
  apply Complex.ext <;>
    simp [geometryFlip,geometryFlipMatrix,geometryEz,spin,pauli,
      alignedState,alignedA,alignedD,alignedC,Matrix.mul_apply,
      Matrix.conjTranspose_apply,Matrix.transpose_apply,Fintype.sum_prod_type,
      Fin.sum_univ_two,Complex.star_def,Complex.mul_re,Complex.mul_im,pow_two]
  all_goals ring

theorem aligned_product_00_00 (c t : ℝ) (z w v : ℂ) :
    (alignedState c t z w v * geometryFlip geometryEz (alignedState c t z w v))
      (0,0) (0,0) = (((1+c+t)*(1-c+t)/16:ℝ):ℂ) -
        (Complex.normSq z:ℂ)-(Complex.normSq w:ℂ) := by
  apply Complex.ext <;>
    simp [geometryFlip,geometryFlipMatrix,geometryEz,spin,pauli,
      alignedState,alignedA,alignedD,alignedC,Matrix.mul_apply,
      Matrix.conjTranspose_apply,Matrix.transpose_apply,Fintype.sum_prod_type,
      Fin.sum_univ_two,Complex.star_def,Complex.mul_re,Complex.mul_im,
      Complex.normSq_apply,pow_two]
  all_goals ring

theorem aligned_product_01_01 (c t : ℝ) (z w v : ℂ) :
    (alignedState c t z w v * geometryFlip geometryEz (alignedState c t z w v))
      (0,1) (0,1) = (((1+c-t)*(1-c-t)/16:ℝ):ℂ) -
        (Complex.normSq z:ℂ)-(Complex.normSq v:ℂ) := by
  apply Complex.ext <;>
    simp [geometryFlip,geometryFlipMatrix,geometryEz,spin,pauli,
      alignedState,alignedA,alignedD,alignedC,Matrix.mul_apply,
      Matrix.conjTranspose_apply,Matrix.transpose_apply,Fintype.sum_prod_type,
      Fin.sum_univ_two,Complex.star_def,Complex.mul_re,Complex.mul_im,
      Complex.normSq_apply,pow_two]
  all_goals ring

theorem aligned_product_00_01 (c t : ℝ) (z w v : ℂ) :
    (alignedState c t z w v * geometryFlip geometryEz (alignedState c t z w v))
      (0,0) (0,1) = w*star z-z*star v := by
  apply Complex.ext <;>
    simp [geometryFlip,geometryFlipMatrix,geometryEz,spin,pauli,
      alignedState,alignedA,alignedD,alignedC,Matrix.mul_apply,
      Matrix.conjTranspose_apply,Matrix.transpose_apply,Fintype.sum_prod_type,
      Fin.sum_univ_two,Complex.star_def,Complex.mul_re,Complex.mul_im,pow_two]
  all_goals ring

/-- Complete equality classification in the actual aligned normal form.
It includes t=0, c=1, and every rank-deficient boundary without division. -/
theorem alignedState_saturation_iff (c t : ℝ) (z w v : ℂ)
    (hM : (alignedState c t z w v).PosSemidef) :
    correlationSq (alignedState c t z w v) = 1-c^2+2*t^2 ↔
      (t:ℂ)*z = 0 ∧
      Complex.normSq z+Complex.normSq w = (1+c+t)*(1-c+t)/16 ∧
      Complex.normSq z+Complex.normSq v = (1+c-t)*(1-c-t)/16 ∧
      z*star v = w*star z := by
  constructor
  · intro he
    have hp := alignedState_saturation_product c t z w v hM he
    have htz := congrArg (fun X : CMatrix => X (0,0) (1,0)) hp
    have hw := congrArg (fun X : CMatrix => X (0,0) (0,0)) hp
    have hv := congrArg (fun X : CMatrix => X (0,1) (0,1)) hp
    have hcross := congrArg (fun X : CMatrix => X (0,0) (0,1)) hp
    dsimp only at htz hw hv hcross
    rw [aligned_product_00_10] at htz
    rw [aligned_product_00_00] at hw
    rw [aligned_product_01_01] at hv
    rw [aligned_product_00_01] at hcross
    simp only [Matrix.zero_apply] at htz hw hv hcross
    have hwr := congrArg Complex.re hw
    have hvr := congrArg Complex.re hv
    norm_num only [Complex.sub_re,Complex.ofReal_re,Complex.zero_re] at hwr hvr
    refine ⟨?_,by linarith,by linarith,?_⟩
    · linear_combination (-2:ℂ)*htz
    · linear_combination -hcross
  · rintro ⟨htz,hw,hv,hcross⟩
    rw [alignedState_correlationSq]
    nlinarith

/-- At strictly positive radial support, every aligned extremizer is an
X-state with both PSD coherence bounds saturated. The two unconstrained
complex phases are retained explicitly, so no optimizer is discarded. -/
theorem alignedState_saturation_pos_iff (c t : ℝ) (z w v : ℂ)
    (hM : (alignedState c t z w v).PosSemidef) (ht : 0 < t) :
    correlationSq (alignedState c t z w v) = 1-c^2+2*t^2 ↔
      z = 0 ∧
      Complex.normSq w = (1+c+t)*(1-c+t)/16 ∧
      Complex.normSq v = (1+c-t)*(1-c-t)/16 := by
  rw [alignedState_saturation_iff c t z w v hM]
  constructor
  · rintro ⟨htz,hw,hv,hcross⟩
    have htC : (t:ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ht
    have hz := (mul_eq_zero.mp htz).resolve_left htC
    refine ⟨hz,?_,?_⟩
    · simpa [hz] using hw
    · simpa [hz] using hv
  · rintro ⟨rfl,hw,hv⟩
    simp [hw,hv]

/-- At zero radial support the equality condition is an exact scaled
unitarity condition on the full complex off-diagonal block, not an
assumption that its diagonal entry vanishes. -/
theorem alignedState_saturation_zero_iff (c : ℝ) (z w v : ℂ)
    (hM : (alignedState c 0 z w v).PosSemidef) :
    correlationSq (alignedState c 0 z w v) = 1-c^2 ↔
      alignedC z w v*(alignedC z w v)ᴴ =
        (((1-c^2)/16:ℝ):ℂ) • (1 : Matrix Q Q ℂ) := by
  constructor
  · intro he
    have hh := (alignedState_saturation_iff c 0 z w v hM).mp (by simpa using he)
    obtain ⟨htz,hw,hv,hcross⟩ := hh
    have hcr := congrArg Complex.re hcross
    have hci := congrArg Complex.im hcross
    simp [Complex.star_def,Complex.mul_re,Complex.mul_im,Complex.normSq_apply] at hw hv hcr hci
    ext i j
    fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
      simp [alignedC,Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.one_apply,
        Fin.sum_univ_two,Complex.star_def,Complex.mul_re,Complex.mul_im,pow_two]
    all_goals nlinarith
  · intro h
    have h0 := congrArg (fun X : Matrix Q Q ℂ => (X 0 0).re) h
    have h1 := congrArg (fun X : Matrix Q Q ℂ => (X 1 1).re) h
    simp [alignedC,Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.one_apply,
      Fin.sum_univ_two,Complex.star_def,Complex.mul_re,Complex.mul_im,pow_two] at h0 h1
    rw [alignedState_correlationSq]
    simp [Complex.normSq_apply]
    nlinarith

end Milne

#print axioms Milne.alignedState_saturation_iff
#print axioms Milne.alignedState_saturation_pos_iff
#print axioms Milne.alignedState_saturation_zero_iff
