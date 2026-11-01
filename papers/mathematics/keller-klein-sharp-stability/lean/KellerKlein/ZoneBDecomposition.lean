import KellerKlein.ZoneBRegions
import KellerKlein.GaussianBaseline
import KellerKlein.ZoneBAlias

noncomputable section
open Set MeasureTheory

namespace KellerKlein

lemma integral_rescale_unit (f : ℝ → ℝ) {a : ℝ} (ha : a ≠ 0) (L R : ℝ) :
    (∫ u in L..R, f u) =
      a / Real.pi * ∫ s in (Real.pi * L / a)..(Real.pi * R / a), f (a * s / Real.pi) := by
  have h := intervalIntegral.smul_integral_comp_mul_left f
    (a := Real.pi * L / a) (b := Real.pi * R / a) (a / Real.pi)
  have hL : a / Real.pi * (Real.pi * L / a) = L := by field_simp [ha, Real.pi_ne_zero]; ring
  have hR : a / Real.pi * (Real.pi * R / a) = R := by field_simp [ha, Real.pi_ne_zero]; ring
  rw [hL, hR] at h
  have hf : (fun s => f (a / Real.pi * s)) = (fun s => f (a * s / Real.pi)) := by
    funext s
    congr 1
    ring
  rw [hf] at h
  simpa only [smul_eq_mul] using h.symm

lemma integral_gaussianKernelUnit {a : ℝ} (ha : 0 < a) (x : ℝ) :
    (∫ u in (0 : ℝ)..1, gaussianKernelUnit a x u) = scaledGaussianKernelIntegral a x := by
  rw [integral_rescale_unit _ ha.ne']
  simp only [mul_zero, zero_div, mul_one]
  have hf : (fun s => gaussianKernelUnit a x (a * s / Real.pi)) =
      (fun s => upperKernel (x / a) (a * s / Real.pi) * gaussian s) := by
    funext s
    unfold gaussianKernelUnit
    congr 1
    congr 1
    field_simp [ha.ne', Real.pi_ne_zero]
  rw [hf, intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ Real.pi / a),
    integral_Ioc_eq_integral_Ioo]
  rfl

lemma integral_envelopeDifference_first {a : ℝ} (ha : 0 < a) (x : ℝ) :
    (∫ u in (0 : ℝ)..(1 / Real.pi), envelopeDifference a x u) = primaryLoss a (x / a) := by
  rw [integral_rescale_unit _ ha.ne']
  have hend : Real.pi * (1 / Real.pi) / a = 1 / a := by field_simp
  rw [mul_zero, zero_div, hend, intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 1 / a),
    integral_Ioc_eq_integral_Ioo]
  unfold primaryLoss
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioo
  intro s hs
  have hu : 0 < a * s / Real.pi := div_pos (mul_pos ha hs.1) Real.pi_pos
  have hu1 : a * s / Real.pi < 1 / Real.pi := by
    apply (div_lt_div_iff_of_pos_right Real.pi_pos).2
    have h := (lt_div_iff₀ ha).1 hs.2
    nlinarith only [h]
  change envelopeDifference a x (a * s / Real.pi) = primaryLossIntegrand a (x / a) s
  rw [envelopeDifference_first (x := x) ha hu hu1]
  have he : Real.pi * (a * s / Real.pi) / a = s := by field_simp [ha.ne', Real.pi_ne_zero]
  rw [he]

lemma integral_aliasKernelUnit {a : ℝ} (ha : 0 < a) (x : ℝ) :
    (∫ u in (crossoverRoot / Real.pi)..1, aliasKernelUnit a x u) =
      zoneBAliasIntegral a (x / a) := by
  rw [integral_rescale_unit _ ha.ne']
  have hend : Real.pi * (crossoverRoot / Real.pi) / a = crossoverRoot / a := by field_simp
  rw [hend, mul_one]
  unfold zoneBAliasIntegral
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  unfold aliasKernelUnit zoneBAliasIntegrand
  congr 1
  congr 1
  field_simp [ha.ne', Real.pi_ne_zero]

lemma intervalIntegrable_sub_unit {f : ℝ → ℝ} (hf : IntervalIntegrable f volume 0 1)
    {L R : ℝ} (hL : 0 ≤ L) (hLR : L ≤ R) (hR : R ≤ 1) :
    IntervalIntegrable f volume L R := by
  apply hf.mono _ le_rfl
  rw [uIcc_of_le hLR, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  intro u hu
  exact ⟨hL.trans hu.1, hu.2.trans hR⟩

lemma integral_envelopeDifference_middle_le {a x : ℝ} (ha : 0 < a) (ha2 : a ≤ 1 / 2) :
    (∫ u in (1 / Real.pi)..(crossoverRoot / Real.pi), envelopeDifference a x u) ≤
      4 * gaussian (1 / a) := by
  have hA : (0 : ℝ) ≤ 1 / Real.pi := by positivity
  have hAB : 1 / Real.pi ≤ crossoverRoot / Real.pi := by
    apply div_le_div_of_nonneg_right _ Real.pi_pos.le
    linarith [crossoverRoot_spec.1, Real.pi_gt_d2]
  have hB : crossoverRoot / Real.pi ≤ 1 := (div_le_one Real.pi_pos).2 crossoverRoot_spec.2.1.le
  have hi := intervalIntegrable_sub_unit (intervalIntegrable_envelopeDifference (x := x) ha (by linarith))
    hA hAB hB
  have hbound : (∫ u in (1 / Real.pi)..(crossoverRoot / Real.pi), envelopeDifference a x u) ≤
      ∫ u in (1 / Real.pi)..(crossoverRoot / Real.pi), (4 * gaussian (1 / a)) := by
    apply intervalIntegral.integral_mono_on_of_le_Ioo hAB hi (continuous_const.intervalIntegrable _ _)
    intro u hu
    exact envelopeDifference_middle_le ha ha2 hu.1.le hu.2.le (hu.2.trans_le hB)
  rw [intervalIntegral.integral_const, smul_eq_mul] at hbound
  have hlen : crossoverRoot / Real.pi - 1 / Real.pi ≤ 1 := by linarith only [hA, hB]
  have hm := mul_le_mul_of_nonneg_right hlen
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (gaussian_nonneg (1 / a)))
  nlinarith only [hbound, hm]

lemma integral_envelopeDifference_alias_le {a x : ℝ} (ha : 0 < a) (ha2 : a ≤ 1 / 2) :
    (∫ u in (crossoverRoot / Real.pi)..1, envelopeDifference a x u) ≤
      zoneBAliasIntegral a (x / a) + 2 * gaussian (1 / a) := by
  have hB0 : 0 ≤ crossoverRoot / Real.pi := by
    apply div_nonneg _ Real.pi_pos.le
    linarith [crossoverRoot_spec.1, Real.pi_pos]
  have hB : crossoverRoot / Real.pi ≤ 1 := (div_le_one Real.pi_pos).2 crossoverRoot_spec.2.1.le
  have hi := intervalIntegrable_sub_unit (intervalIntegrable_envelopeDifference (x := x) ha (by linarith))
    hB0 hB le_rfl
  have hAlias := intervalIntegrable_sub_unit (intervalIntegrable_aliasKernelUnit a x) hB0 hB le_rfl
  have hconst : IntervalIntegrable (fun _ : ℝ => 2 * gaussian (1 / a)) volume
      (crossoverRoot / Real.pi) 1 := continuous_const.intervalIntegrable _ _
  have hbound : (∫ u in (crossoverRoot / Real.pi)..1, envelopeDifference a x u) ≤
      ∫ u in (crossoverRoot / Real.pi)..1, aliasKernelUnit a x u + 2 * gaussian (1 / a) := by
    apply intervalIntegral.integral_mono_on_of_le_Ioo hB hi (hAlias.add hconst)
    intro u hu
    exact envelopeDifference_alias_le ha hu.1 hu.2
  rw [intervalIntegral.integral_add hAlias hconst, integral_aliasKernelUnit ha,
    intervalIntegral.integral_const, smul_eq_mul] at hbound
  have hlen : 1 - crossoverRoot / Real.pi ≤ 1 := by linarith only [hB0]
  have hm := mul_le_mul_of_nonneg_right hlen
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (gaussian_nonneg (1 / a)))
  nlinarith only [hbound, hm]

theorem JUpper_le_gaussian_primary_alias {a x : ℝ} (ha : 0 < a) (ha2 : a ≤ 1 / 2)
    (hx : 0 ≤ x) :
    JUpper a x ≤ scaledGaussianKernelIntegral a x + primaryLoss a (x / a) +
      zoneBAliasIntegral a (x / a) + 6 * gaussian (1 / a) := by
  have hA : (0 : ℝ) ≤ 1 / Real.pi := by positivity
  have hAB : 1 / Real.pi ≤ crossoverRoot / Real.pi := by
    apply div_le_div_of_nonneg_right _ Real.pi_pos.le
    linarith [crossoverRoot_spec.1, Real.pi_gt_d2]
  have hB : crossoverRoot / Real.pi ≤ 1 := (div_le_one Real.pi_pos).2 crossoverRoot_spec.2.1.le
  have hi := intervalIntegrable_envelopeDifference (x := x) ha (by linarith)
  have h01 := intervalIntegrable_sub_unit hi le_rfl hA (hAB.trans hB)
  have h12 := intervalIntegrable_sub_unit hi hA hAB hB
  have h23 := intervalIntegrable_sub_unit hi (hA.trans hAB) hB le_rfl
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (h01.trans h12) h23
  rw [← intervalIntegral.integral_add_adjacent_intervals h01 h12] at hsplit
  have hbase : (∫ u in (0 : ℝ)..1, envelopeDifference a x u) =
      JUpper a x - scaledGaussianKernelIntegral a x := by
    change (∫ u in (0 : ℝ)..1, upperEnvelopeIntegrand a x u - gaussianKernelUnit a x u) = _
    rw [intervalIntegral.integral_sub
      (intervalIntegrable_upperEnvelopeIntegrand ha (by linarith))
      (intervalIntegrable_gaussianKernelUnit a x), integral_gaussianKernelUnit ha]
    rfl
  rw [hbase, integral_envelopeDifference_first ha] at hsplit
  have hmid := integral_envelopeDifference_middle_le (x := x) ha ha2
  have halias := integral_envelopeDifference_alias_le (x := x) ha ha2
  linarith only [hsplit, hmid, halias]

end KellerKlein
