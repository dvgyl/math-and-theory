import KellerKlein.GaussianFourier

noncomputable section

open Set MeasureTheory Filter
open scoped Topology

namespace KellerKlein

set_option maxHeartbeats 800000

def gaussianTailMoment (k : ℕ) (R : ℝ) : ℝ :=
  ∫ s in Ioi R, s ^ k * gaussian s

lemma gaussianTailMoment_nonneg (k : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    0 ≤ gaussianTailMoment k R := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  exact mul_nonneg (pow_nonneg (le_trans hR hs.le) _) (gaussian_nonneg s)

lemma gaussianTailMoment_le_halfMoment (k : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    gaussianTailMoment k R ≤ halfMoment k := by
  apply setIntegral_mono_set (integrableOn_pow_gaussian k)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact mul_nonneg (pow_nonneg hs.le _) (gaussian_nonneg s)
  · exact Filter.Eventually.of_forall (Ioi_subset_Ioi hR)

lemma gaussianTailMoment_one (R : ℝ) : gaussianTailMoment 1 R = gaussian R := by
  have hd : ∀ s ∈ Ici R, HasDerivAt gaussian (-(s * gaussian s)) s := by
    intro s hs
    simpa only [neg_mul] using hasDerivAt_gaussian s
  have hi : IntegrableOn (fun s => -(s * gaussian s)) (Ioi R) := by
    simpa only [pow_one] using (integrable_pow_gaussian 1).integrableOn.neg
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' hd hi tendsto_gaussian
  rw [integral_neg] at h
  have h' : -gaussianTailMoment 1 R = 0-gaussian R := by
    simpa only [gaussianTailMoment, pow_one] using h
  linarith

lemma gaussianTailMoment_zero_le {R : ℝ} (hR : 0 < R) :
    gaussianTailMoment 0 R ≤ gaussian R / R := by
  apply (le_div_iff₀ hR).2
  have h : R * gaussianTailMoment 0 R ≤ gaussianTailMoment 1 R := by
    rw [gaussianTailMoment, ← integral_const_mul]
    apply integral_mono_ae
      ((integrable_pow_gaussian 0).integrableOn.const_mul R)
      (integrable_pow_gaussian 1).integrableOn
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    simpa only [pow_zero, one_mul, pow_one] using
      mul_le_mul_of_nonneg_right hs.le (gaussian_nonneg s)
  rw [gaussianTailMoment_one] at h
  nlinarith

lemma gaussianTailMoment_two (R : ℝ) :
    gaussianTailMoment 2 R = R * gaussian R + gaussianTailMoment 0 R := by
  let f : ℝ → ℝ := fun s => s * gaussian s
  let f' : ℝ → ℝ := fun s => gaussian s - s^2 * gaussian s
  have hd : ∀ s ∈ Ici R, HasDerivAt f (f' s) s := by
    intro s hs
    convert (hasDerivAt_id s).mul (hasDerivAt_gaussian s) using 1 <;>
      dsimp [f, f'] <;> ring
  have h0 : IntegrableOn gaussian (Ioi R) := integrable_gaussian.integrableOn
  have h2 := (integrable_pow_gaussian 2).integrableOn (s := Ioi R)
  have hi : IntegrableOn f' (Ioi R) := h0.sub h2
  have ht : Tendsto f atTop (𝓝 0) := by
    simpa only [f, pow_one] using tendsto_pow_gaussian 1
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' hd hi ht
  change (∫ s in Ioi R, gaussian s - s^2 * gaussian s) = 0 - R * gaussian R at h
  rw [integral_sub h0 h2] at h
  have hz : (∫ s in Ioi R, gaussian s) = gaussianTailMoment 0 R := by
    simp only [gaussianTailMoment, pow_zero, one_mul]
  rw [hz] at h
  change gaussianTailMoment 0 R - gaussianTailMoment 2 R = 0 - R * gaussian R at h
  linarith

lemma gaussianTailMoment_two_le {R : ℝ} (hR : 0 < R) :
    gaussianTailMoment 2 R ≤ (R + 1/R) * gaussian R := by
  rw [gaussianTailMoment_two]
  have h := gaussianTailMoment_zero_le hR
  calc
    R*gaussian R+gaussianTailMoment 0 R ≤ R*gaussian R+gaussian R/R :=
      add_le_add_left h _
    _ = (R+1/R)*gaussian R := by ring

lemma gaussian_antitoneOn : AntitoneOn gaussian (Ici (0 : ℝ)) := by
  intro x hx y hy hxy
  have hx0 : 0 ≤ x := hx
  have hy0 : 0 ≤ y := hy
  apply Real.exp_le_exp.mpr
  dsimp [gaussian]
  nlinarith

end KellerKlein
