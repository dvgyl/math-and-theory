import MilneAlignedState
import MilneGeometryInterval

open scoped BigOperators Matrix ComplexOrder
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 16000

noncomputable section
namespace Milne

def radialVolumeCap (c t : ℝ) : ℝ := t*((1+t)^2-c^2)/4

def tripleVolumeCap (c t τ : ℝ) : ℝ :=
  (t/2)*min (τ-t^2) (1+2*t+2*t^2-c^2-τ)

theorem alignedT_determinant (t : ℝ) (z w v : ℂ) :
    (alignedT t z w v).det = 4*t*(Complex.normSq v-Complex.normSq w) := by
  rw [Matrix.det_fin_three]
  simp [alignedT,Complex.normSq_apply]
  ring

theorem alignedState_determinant (c t : ℝ) (z w v : ℂ) :
    Matrix.det (correlation (alignedState c t z w v)) =
      4*t*(Complex.normSq v-Complex.normSq w) := by
  rw [alignedState_bloch,blochState_correlations,alignedT_determinant]

/-- Exact signed determinant bounds from two actual principal minors. -/
theorem alignedState_signed_determinant_bounds {c t : ℝ} {z w v : ℂ}
    (ht0 : 0 ≤ t) (hM : (alignedState c t z w v).PosSemidef) :
    -radialVolumeCap c t ≤ Matrix.det (correlation (alignedState c t z w v)) ∧
    Matrix.det (correlation (alignedState c t z w v)) ≤ t*((1-t)^2-c^2)/4 := by
  have hw := alignedState_minor_w c t z w v hM
  have hv := alignedState_minor_v c t z w v hM
  have hw0 := Complex.normSq_nonneg w
  have hv0 := Complex.normSq_nonneg v
  have hlow := mul_le_mul_of_nonneg_left hw (show 0 ≤ 4*t by linarith)
  have hupp := mul_le_mul_of_nonneg_left hv (show 0 ≤ 4*t by linarith)
  have hwp := mul_nonneg ht0 hw0
  have hvp := mul_nonneg ht0 hv0
  rw [alignedState_determinant]
  unfold radialVolumeCap
  constructor <;> nlinarith

/-- Sharp absolute determinant bound in actual radial coordinates. -/
theorem alignedState_volume_bound {c t : ℝ} {z w v : ℂ}
    (ht0 : 0 ≤ t) (hM : (alignedState c t z w v).PosSemidef) :
    |Matrix.det (correlation (alignedState c t z w v))| ≤ radialVolumeCap c t := by
  have h := alignedState_signed_determinant_bounds ht0 hM
  apply abs_le.mpr
  refine ⟨h.1,?_⟩
  have hdiff : t*((1-t)^2-c^2)/4 ≤ radialVolumeCap c t := by
    unfold radialVolumeCap
    nlinarith [sq_nonneg t]
  exact h.2.trans hdiff

/-- A rank-safe bound on the first off-diagonal row. Its proof uses one
explicit quadratic-form test, not an inverse Schur complement. -/
theorem alignedState_row0_bound {c t : ℝ} {z w v : ℂ}
    (hc1 : c ≤ 1) (ht0 : 0 ≤ t)
    (hM : (alignedState c t z w v).PosSemidef) :
    Complex.normSq z+Complex.normSq w ≤ (1+c+t)*(1-c+t)/16 := by
  let d := (1-c+t)/4
  have hd0 : 0 ≤ d := by dsimp [d]; linarith
  have hZ := Complex.normSq_nonneg z
  have hW := Complex.normSq_nonneg w
  by_cases hd : d = 0
  · have hmz := alignedState_minor_z c t z w v hM
    have hmw := alignedState_minor_w c t z w v hM
    have hct : c = 1 ∧ t = 0 := by dsimp [d] at hd; constructor <;> linarith
    rcases hct with ⟨rfl,rfl⟩
    norm_num at hmz hmw ⊢
    linarith
  · have hdp : 0 < d := lt_of_le_of_ne hd0 (Ne.symm hd)
    let q : QQ → ℂ := fun i =>
      if i = (0,0) then (d:ℂ) else
      if i = (1,0) then -star z else if i = (1,1) then -star w else 0
    have h := hM.re_dotProduct_nonneg q
    have hid : (dotProduct (star q) ((alignedState c t z w v) *ᵥ q)).re =
        d*((1+c+t)*(1-c+t)/16-Complex.normSq z-Complex.normSq w)-
          (t/2)*Complex.normSq z := by
      simp [q,dotProduct,Matrix.mulVec,alignedState,alignedA,alignedD,alignedC,
        Fintype.sum_prod_type,Fin.sum_univ_two,Complex.star_def,Complex.mul_re,
        Complex.mul_im,Complex.normSq_apply]
      dsimp [d]
      ring
    change 0 ≤ (dotProduct (star q) ((alignedState c t z w v) *ᵥ q)).re at h
    rw [hid] at h
    have hp := mul_nonneg ht0 hZ
    have hs : 0 ≤ d*((1+c+t)*(1-c+t)/16-Complex.normSq z-Complex.normSq w) := by
      linarith
    have hq := (mul_nonneg_iff_of_pos_left hdp).mp hs
    linarith

/-- The second off-diagonal row obeys the same universal cap. -/
theorem alignedState_row1_bound {c t : ℝ} {z w v : ℂ}
    (hc1 : c ≤ 1) (ht0 : 0 ≤ t)
    (hM : (alignedState c t z w v).PosSemidef) :
    Complex.normSq z+Complex.normSq v ≤ (1+c+t)*(1-c+t)/16 := by
  let d := (1-c+t)/4
  have hd0 : 0 ≤ d := by dsimp [d]; linarith
  have hZ := Complex.normSq_nonneg z
  have hV := Complex.normSq_nonneg v
  by_cases hd : d = 0
  · have hmz := alignedState_minor_z c t z w v hM
    have hmv := alignedState_minor_v c t z w v hM
    have hct : c = 1 ∧ t = 0 := by dsimp [d] at hd; constructor <;> linarith
    rcases hct with ⟨rfl,rfl⟩
    norm_num at hmz hmv ⊢
    linarith
  · have hdp : 0 < d := lt_of_le_of_ne hd0 (Ne.symm hd)
    let q : QQ → ℂ := fun i =>
      if i = (0,1) then (d:ℂ) else
      if i = (1,0) then -star v else if i = (1,1) then star z else 0
    have h := hM.re_dotProduct_nonneg q
    have hid : (dotProduct (star q) ((alignedState c t z w v) *ᵥ q)).re =
        d*((1+c-t)*(1-c+t)/16-Complex.normSq z-Complex.normSq v)-
          (t/2)*Complex.normSq v := by
      simp [q,dotProduct,Matrix.mulVec,alignedState,alignedA,alignedD,alignedC,
        Fintype.sum_prod_type,Fin.sum_univ_two,Complex.star_def,Complex.mul_re,
        Complex.mul_im,Complex.normSq_apply]
      dsimp [d]
      ring
    change 0 ≤ (dotProduct (star q) ((alignedState c t z w v) *ᵥ q)).re at h
    rw [hid] at h
    have hp := mul_nonneg ht0 hV
    have hs : 0 ≤ d*((1+c-t)*(1-c+t)/16-Complex.normSq z-Complex.normSq v) := by
      linarith
    have hq := (mul_nonneg_iff_of_pos_left hdp).mp hs
    have hprod : 0 ≤ t*(1-c+t) := mul_nonneg ht0 (by linarith)
    nlinarith

/-- Sharp tent-shaped upper tradeoff between volume and correlation, for
an actual positive density matrix, including zero diagonal blocks. -/
theorem alignedState_triple_volume_bound {c t : ℝ} {z w v : ℂ}
    (hc1 : c ≤ 1) (ht0 : 0 ≤ t)
    (hM : (alignedState c t z w v).PosSemidef) :
    |Matrix.det (correlation (alignedState c t z w v))| ≤
      tripleVolumeCap c t (correlationSq (alignedState c t z w v)) := by
  have hZ := Complex.normSq_nonneg z
  have hW := Complex.normSq_nonneg w
  have hV := Complex.normSq_nonneg v
  have h0 := alignedState_row0_bound hc1 ht0 hM
  have h1 := alignedState_row1_bound hc1 ht0 hM
  have hfirst : |Complex.normSq v-Complex.normSq w| ≤
      Complex.normSq w+Complex.normSq v+2*Complex.normSq z := by
    apply abs_le.mpr
    constructor <;> linarith
  have hsecond : |Complex.normSq v-Complex.normSq w| ≤
      2*((1+c+t)*(1-c+t)/16)-
        (Complex.normSq w+Complex.normSq v+2*Complex.normSq z) := by
    apply abs_le.mpr
    constructor <;> linarith
  have hp0 := mul_le_mul_of_nonneg_left hfirst (show 0 ≤ 4*t by linarith)
  have hp1 := mul_le_mul_of_nonneg_left hsecond (show 0 ≤ 4*t by linarith)
  rw [alignedState_determinant,abs_mul,abs_of_nonneg (show 0 ≤ 4*t by linarith)]
  rw [tripleVolumeCap,alignedState_correlationSq,mul_min_of_nonneg _ _ (by linarith : 0 ≤ t/2)]
  apply le_min
  · nlinarith
  · nlinarith

end Milne

#print axioms Milne.alignedState_volume_bound
#print axioms Milne.alignedState_triple_volume_bound
