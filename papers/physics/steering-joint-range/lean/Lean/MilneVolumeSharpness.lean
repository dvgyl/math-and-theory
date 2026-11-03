import MilneVolumeGeometry

open scoped BigOperators Matrix ComplexOrder
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 16000

noncomputable section
namespace Milne

def volumeWitness (c t : ℝ) : CMatrix :=
  (1/4:ℂ) • pure (geometrySkewPlus c t) +
    Matrix.diagonal (fun i : QQ =>
      if i = (0,1) then (((1+c-t)/4:ℝ):ℂ) else
      if i = (1,0) then (((1-c-t)/4:ℝ):ℂ) else 0)

theorem volumeWitness_psd {c t : ℝ}
    (hc0 : 0 ≤ c) (ht1 : t ≤ 1-c) : (volumeWitness c t).PosSemidef := by
  have hb : (0:ℝ) ≤ (1+c-t)/4 := by linarith
  have he : (0:ℝ) ≤ (1-c-t)/4 := by linarith
  unfold volumeWitness
  apply Matrix.PosSemidef.add
  · simpa using psd_real_smul (pure_psd (geometrySkewPlus c t)) (1/4) (by norm_num)
  · apply Matrix.posSemidef_diagonal_iff.mpr
    intro i
    by_cases h01 : i = (0,1)
    · rw [if_pos h01]
      exact RCLike.ofReal_nonneg.mpr hb
    · rw [if_neg h01]
      by_cases h10 : i = (1,0)
      · rw [if_pos h10]
        exact RCLike.ofReal_nonneg.mpr he
      · rw [if_neg h10]

theorem volumeWitness_aligned {c t : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (ht0 : 0 ≤ t) :
    volumeWitness c t = alignedState c t 0 ((geometrySkewU c t/4:ℝ):ℂ) 0 := by
  have h0 := Real.sq_sqrt (show 0 ≤ 1+c+t by linarith)
  have h1 := Real.sq_sqrt (show 0 ≤ 1-c+t by linarith)
  have h0C : (Real.sqrt (1+c+t):ℂ)^2 = (1+c+t:ℂ) := by exact_mod_cast h0
  have h1C : (Real.sqrt (1-c+t):ℂ)^2 = (1-c+t:ℂ) := by exact_mod_cast h1
  ext ⟨i,k⟩ ⟨j,l⟩
  fin_cases i <;> fin_cases k <;> fin_cases j <;> fin_cases l <;>
    apply Complex.ext <;>
    simp [volumeWitness,alignedState,alignedA,alignedD,alignedC,
      geometrySkewPlus,geometrySkewU,pure,Matrix.diagonal_apply,
      Complex.star_def,Complex.mul_re,Complex.mul_im,Prod.ext_iff,
      ← pow_two,h0,h1,h0C,h1C]
  all_goals ring

theorem geometrySkewU_div_four_sq {c t : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (ht0 : 0 ≤ t) :
    (geometrySkewU c t/4)^2 = ((1+t)^2-c^2)/16 := by
  have h0 := Real.sq_sqrt (show 0 ≤ 1+c+t by linarith)
  have h1 := Real.sq_sqrt (show 0 ≤ 1-c+t by linarith)
  unfold geometrySkewU
  rw [div_pow,mul_pow,h0,h1]
  ring

theorem geometrySkewV_div_four_sq {c t : ℝ}
    (hc0 : 0 ≤ c) (ht1 : t ≤ 1-c) :
    (geometrySkewV c t/4)^2 = ((1-t)^2-c^2)/16 := by
  have h0 := Real.sq_sqrt (show 0 ≤ 1+c-t by linarith)
  have h1 := Real.sq_sqrt (show 0 ≤ 1-c-t by linarith)
  unfold geometrySkewV
  rw [div_pow,mul_pow,h0,h1]
  ring

theorem geometryDiagonalState_aligned (c t : ℝ) :
    geometryDiagonalState c t = alignedState c t 0 0 0 := by
  rw [geometryDiagonalState_bloch,alignedState_bloch]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [geometryDiagonalT,alignedT]

theorem geometrySkewState_aligned {c t : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1-c) :
    geometrySkewState c t =
      alignedState c t 0 ((geometrySkewU c t/4:ℝ):ℂ) ((geometrySkewV c t/4:ℝ):ℂ) := by
  rw [geometrySkewState_bloch hc0 hc1 ht0 ht1,alignedState_bloch]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [geometrySkewT,alignedT]
  all_goals ring

theorem alignedState_affine (c t α : ℝ) (z₀ w₀ v₀ z₁ w₁ v₁ : ℂ) :
    (((1-α:ℝ):ℂ) • alignedState c t z₀ w₀ v₀ +
      (α:ℂ) • alignedState c t z₁ w₁ v₁) =
      alignedState c t (((1-α:ℝ):ℂ)*z₀+(α:ℂ)*z₁)
        (((1-α:ℝ):ℂ)*w₀+(α:ℂ)*w₁)
        (((1-α:ℝ):ℂ)*v₀+(α:ℂ)*v₁) := by
  ext ⟨i,k⟩ ⟨j,l⟩
  fin_cases i <;> fin_cases k <;> fin_cases j <;> fin_cases l <;>
    apply Complex.ext <;>
    simp [alignedState,alignedA,alignedD,alignedC,Complex.mul_re,
      Complex.mul_im,Complex.star_def]
  all_goals ring

/-- Independent control of the first coherence, with the second set to zero. -/
theorem volumeLowerFamily_psd {c t α : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1-c)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    (alignedState c t 0 ((α*(geometrySkewU c t/4):ℝ):ℂ) 0).PosSemidef := by
  have h := (psd_real_smul (geometryDiagonalState_psd hc0 hc1 ht0 ht1)
    (1-α) (by linarith)).add (psd_real_smul (volumeWitness_psd hc0 ht1) α hα0)
  rw [geometryDiagonalState_aligned,volumeWitness_aligned hc0 hc1 ht0,alignedState_affine] at h
  simpa using h

/-- Once the first coherence is saturated, the second can vary independently. -/
theorem volumeUpperFamily_psd {c t β : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1-c)
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    (alignedState c t 0 ((geometrySkewU c t/4:ℝ):ℂ)
      ((β*(geometrySkewV c t/4):ℝ):ℂ)).PosSemidef := by
  have h := (psd_real_smul (volumeWitness_psd hc0 ht1)
    (1-β) (by linarith)).add (psd_real_smul (geometrySkewState_psd c t) β hβ0)
  rw [volumeWitness_aligned hc0 hc1 ht0,geometrySkewState_aligned hc0 hc1 ht0 ht1,
    alignedState_affine] at h
  have he : ((1-β:ℝ):ℂ)*(geometrySkewU c t/4:ℝ)+(β:ℂ)*(geometrySkewU c t/4:ℝ) =
      (geometrySkewU c t/4:ℝ) := by push_cast; ring
  rw [he] at h
  simpa using h

theorem exists_unit_scale_square {U s : ℝ}
    (hU0 : 0 ≤ U) (hs0 : 0 ≤ s) (hsU : s ≤ U) :
    ∃ α : ℝ, 0 ≤ α ∧ α ≤ 1 ∧ α^2*U = s := by
  by_cases hU : U = 0
  · have hs : s = 0 := le_antisymm (by simpa [hU] using hsU) hs0
    exact ⟨0,by norm_num,by norm_num,by simp [hs]⟩
  · have hUp : 0 < U := lt_of_le_of_ne hU0 (Ne.symm hU)
    have hq0 := div_nonneg hs0 hU0
    have hq1 : s/U ≤ 1 := (div_le_iff₀ hUp).mpr (by simpa using hsU)
    have hsq := Real.sq_sqrt hq0
    refine ⟨Real.sqrt (s/U),Real.sqrt_nonneg _,by nlinarith,?_⟩
    rw [hsq,div_mul_cancel₀ _ hU]

/-- The feasible determinant magnitudes at prescribed canonical data,
quantifying an actual positive four-by-four state in radial coordinates. -/
def alignedTripleVolumeSpectrum (c t τ : ℝ) : Set ℝ :=
  {q | ∃ z w v : ℂ, (alignedState c t z w v).PosSemidef ∧
    correlationSq (alignedState c t z w v) = τ ∧
    |Matrix.det (correlation (alignedState c t z w v))| = q}

/-- Every point of the sharp triple-parameter volume curve is realized by
an actual PSD canonical state. The two branches vary separate coherences. -/
theorem alignedTripleVolumeSpectrum_attained {c t τ : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1-c)
    (hτ0 : t^2 ≤ τ) (hτ1 : τ ≤ 1-c^2+2*t^2) :
    tripleVolumeCap c t τ ∈ alignedTripleVolumeSpectrum c t τ := by
  let u := geometrySkewU c t/4
  let v := geometrySkewV c t/4
  let U := u^2
  let V := v^2
  let s := (τ-t^2)/8
  have hU0 : 0 ≤ U := sq_nonneg u
  have hV0 : 0 ≤ V := sq_nonneg v
  have hU : U = ((1+t)^2-c^2)/16 := geometrySkewU_div_four_sq hc0 hc1 ht0
  have hV : V = ((1-t)^2-c^2)/16 := geometrySkewV_div_four_sq hc0 ht1
  have hs0 : 0 ≤ s := by dsimp [s]; linarith
  have hsUV : s ≤ U+V := by rw [hU,hV]; dsimp [s]; nlinarith
  have hUV : V ≤ U := by rw [hU,hV]; nlinarith
  by_cases hsU : s ≤ U
  · rcases exists_unit_scale_square hU0 hs0 hsU with ⟨α,hα0,hα1,hα⟩
    have hcap : tripleVolumeCap c t τ = 4*t*s := by
      have hmin : τ-t^2 ≤ 1+2*t+2*t^2-c^2-τ := by
        rw [hU] at hsU
        dsimp [s] at hsU
        nlinarith
      rw [tripleVolumeCap,min_eq_left hmin]
      dsimp [s]
      ring
    refine ⟨0,((α*u:ℝ):ℂ),0,volumeLowerFamily_psd hc0 hc1 ht0 ht1 hα0 hα1,?_,?_⟩
    · rw [alignedState_correlationSq]
      simp only [Complex.normSq_zero,Complex.normSq_ofReal,← pow_two,mul_zero,add_zero,zero_add]
      rw [mul_pow]
      change t^2+8*(α^2*U) = τ
      rw [hα]
      dsimp [s]
      ring
    · rw [alignedState_determinant]
      simp only [Complex.normSq_zero,Complex.normSq_ofReal,← pow_two]
      rw [mul_pow]
      change |4*t*(0-α^2*U)| = tripleVolumeCap c t τ
      rw [hα,hcap]
      have hn : 4*t*(0-s) ≤ 0 := by nlinarith [mul_nonneg ht0 hs0]
      rw [abs_of_nonpos hn]
      ring
  · have hUs : U ≤ s := le_of_not_ge hsU
    have hdiff0 : 0 ≤ s-U := by linarith
    have hdiffV : s-U ≤ V := by linarith
    rcases exists_unit_scale_square hV0 hdiff0 hdiffV with ⟨β,hβ0,hβ1,hβ⟩
    have hcap : tripleVolumeCap c t τ = 4*t*(2*U-s) := by
      have hmin : 1+2*t+2*t^2-c^2-τ ≤ τ-t^2 := by
        rw [hU] at hUs
        dsimp [s] at hUs
        nlinarith
      rw [tripleVolumeCap,min_eq_right hmin,hU]
      dsimp [s]
      ring
    refine ⟨0,(u:ℂ),((β*v:ℝ):ℂ),volumeUpperFamily_psd hc0 hc1 ht0 ht1 hβ0 hβ1,?_,?_⟩
    · rw [alignedState_correlationSq]
      simp only [Complex.normSq_zero,Complex.normSq_ofReal,← pow_two,mul_zero,zero_add,add_zero]
      rw [mul_pow]
      change t^2+8*U+8*(β^2*V) = τ
      rw [hβ]
      dsimp [s]
      ring
    · rw [alignedState_determinant]
      simp only [Complex.normSq_ofReal,← pow_two]
      rw [mul_pow]
      change |4*t*(β^2*V-U)| = tripleVolumeCap c t τ
      rw [hβ,hcap]
      have hgap : 0 ≤ 2*U-s := by linarith
      have hn : 4*t*(s-U-U) ≤ 0 := by nlinarith [mul_nonneg ht0 hgap]
      rw [abs_of_nonpos hn]
      ring

/-- Exact maximum of volume at a fixed canonical centre, radial width and
correlation norm, with an actual-state domain and physical witnesses. -/
theorem alignedTripleVolumeSpectrum_isGreatest {c t τ : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1-c)
    (hτ0 : t^2 ≤ τ) (hτ1 : τ ≤ 1-c^2+2*t^2) :
    IsGreatest (alignedTripleVolumeSpectrum c t τ) (tripleVolumeCap c t τ) := by
  refine ⟨alignedTripleVolumeSpectrum_attained hc0 hc1 ht0 ht1 hτ0 hτ1,?_⟩
  rintro q ⟨z,w,v,hM,hτ,hq⟩
  have h := alignedState_triple_volume_bound hc1 ht0 hM
  rwa [hτ,hq] at h

/-- The volume maximum at fixed c,t is attained by the explicit rank-three
X family (with the usual lower-rank endpoint reductions). -/
theorem volumeWitness_attains {c t : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1-c) :
    Density (volumeWitness c t) ∧
    geometryLocalA (volumeWitness c t) = c • geometryEz ∧
    geometryLocalB (volumeWitness c t) = 0 ∧
    vSq (ttVec (correlation (volumeWitness c t)) geometryEz) = t^2 ∧
    |Matrix.det (correlation (volumeWitness c t))| = radialVolumeCap c t := by
  rw [volumeWitness_aligned hc0 hc1 ht0]
  refine ⟨alignedState_density _ _ _ _ _ (by
    rw [← volumeWitness_aligned hc0 hc1 ht0]
    exact volumeWitness_psd hc0 ht1),?_,?_,?_,?_⟩
  · rw [alignedState_bloch,geometryLocalA_blochState]
  · rw [alignedState_bloch,geometryLocalB_blochState]
  · rw [alignedState_bloch,blochState_correlations,alignedT_radial]
  · rw [alignedState_determinant]
    simp only [Complex.normSq_zero,Complex.normSq_ofReal,← pow_two,zero_sub]
    have hu := geometrySkewU_div_four_sq hc0 hc1 ht0
    have hn : 4*t*(-(geometrySkewU c t/4)^2) ≤ 0 := by
      nlinarith [mul_nonneg ht0 (sq_nonneg (geometrySkewU c t/4))]
    rw [abs_of_nonpos hn,hu]
    unfold radialVolumeCap
    ring

end Milne

#print axioms Milne.alignedTripleVolumeSpectrum_isGreatest
#print axioms Milne.volumeWitness_attains
