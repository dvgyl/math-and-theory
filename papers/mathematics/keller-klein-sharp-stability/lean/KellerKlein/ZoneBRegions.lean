import KellerKlein.EnvelopeIntegral
import KellerKlein.ZoneBIntegral
import KellerKlein.ZoneAProfile

noncomputable section
open Set MeasureTheory

namespace KellerKlein

def gaussianKernelUnit (a x u : ℝ) : ℝ :=
  upperKernel (x / a) u * gaussian (Real.pi * u / a)

def envelopeDifference (a x u : ℝ) : ℝ :=
  upperEnvelopeIntegrand a x u - gaussianKernelUnit a x u

def aliasKernelUnit (a x u : ℝ) : ℝ :=
  |upperKernel (x / a) u| * cosineProfile a (Real.pi * u / a)

lemma max_kernel_loss (k l g : ℝ) (hlg : l ≤ g) :
    max (k * l) (k * g) = k * g + max 0 (-k) * (g - l) := by
  by_cases hk : 0 ≤ k
  · rw [max_eq_right (mul_le_mul_of_nonneg_left hlg hk), max_eq_left (by linarith : -k ≤ 0)]
    ring
  · have hk' : k ≤ 0 := (lt_of_not_ge hk).le
    rw [max_eq_left (mul_le_mul_of_nonpos_left hlg hk'), max_eq_right (by linarith : 0 ≤ -k)]
    ring

lemma max_kernel_symmetric (k p : ℝ) (hp : 0 ≤ p) :
    max (k * (-p)) (k * p) = |k| * p := by
  by_cases hk : 0 ≤ k
  · rw [abs_of_nonneg hk, max_eq_right (by nlinarith [mul_nonneg hk hp])]
  · have hk' : k ≤ 0 := (lt_of_not_ge hk).le
    rw [abs_of_nonpos hk', max_eq_left (by nlinarith [mul_nonpos_of_nonpos_of_nonneg hk' hp])]
    ring

lemma intervalIntegrable_gaussianKernelUnit (a x : ℝ) :
    IntervalIntegrable (gaussianKernelUnit a x) volume 0 1 := by
  apply (intervalIntegrable_upperKernel (x / a)).mul_continuousOn
  exact (continuous_gaussian.comp
    ((continuous_const.mul continuous_id).div_const a)).continuousOn

lemma intervalIntegrable_envelopeDifference {a x : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    IntervalIntegrable (envelopeDifference a x) volume 0 1 :=
  (intervalIntegrable_upperEnvelopeIntegrand ha ha1).sub (intervalIntegrable_gaussianKernelUnit a x)

lemma intervalIntegrable_aliasKernelUnit (a x : ℝ) :
    IntervalIntegrable (aliasKernelUnit a x) volume 0 1 := by
  apply (intervalIntegrable_upperKernel (x / a)).abs.mul_continuousOn
  exact ((continuous_cosineProfile a).comp
    ((continuous_const.mul continuous_id).div_const a)).continuousOn

lemma envelopeDifference_first {a x u : ℝ} (ha : 0 < a)
    (hu : 0 < u) (hu1 : u < 1 / Real.pi) :
    envelopeDifference a x u = primaryLossIntegrand a (x / a) (Real.pi * u / a) := by
  have ht : 0 < Real.pi * u / a := by positivity
  have hphase : a * (Real.pi * u / a) = Real.pi * u := by field_simp [ha.ne']
  have hy1 : Real.pi * u < 1 := by
    have h := (lt_div_iff₀ Real.pi_pos).1 hu1
    simpa [mul_comm] using h
  have hhalf : a * (Real.pi * u / a) < Real.pi / 2 := by
    rw [hphase]
    linarith [Real.pi_gt_d2]
  have hroot : a * (Real.pi * u / a) ≤ crossoverRoot := hhalf.le.trans crossoverRoot_spec.1.le
  have hP := cosine_profile_le_gaussian ha ht.le hhalf
  have hU : a * (Real.pi * u / a) / Real.pi = u := by
    field_simp [ha.ne', Real.pi_ne_zero]
  unfold envelopeDifference upperEnvelopeIntegrand gaussianKernelUnit
  rw [lowerEnvelope, if_pos hhalf.le, upperEnvelope, if_pos hroot]
  change max (upperKernel (x / a) u * Real.cos (a * (Real.pi * u / a)) ^ (1 / a ^ 2 : ℝ))
      (upperKernel (x / a) u * gaussian (Real.pi * u / a)) -
      upperKernel (x / a) u * gaussian (Real.pi * u / a) = _
  rw [max_kernel_loss _ _ _ hP]
  unfold primaryLossIntegrand
  rw [hU]
  ring

lemma gaussian_le_inv_scale {a s : ℝ} (ha : 0 < a) (hs : 1 / a ≤ s) :
    gaussian s ≤ gaussian (1 / a) := by
  have hs0 : 0 ≤ 1 / a := by positivity
  have hsq := pow_le_pow_left₀ hs0 hs 2
  unfold gaussian
  exact Real.exp_le_exp.mpr (by linarith only [hsq])

lemma slow_gaussian_le_inv_scale {a s : ℝ} (ha : 0 < a) (ha2 : a ≤ 1 / 2)
    (hs : Real.pi / (2 * a) ≤ s) :
    Real.exp (-(1 - a ^ 2) * s ^ 2 / 2) ≤ gaussian (1 / a) := by
  have haSq : a ^ 2 ≤ 1 / 4 := by nlinarith
  have hs0 : 0 < s := (div_pos Real.pi_pos (mul_pos (by norm_num) ha)).trans_le hs
  have hmul : Real.pi ≤ s * (2 * a) := (div_le_iff₀ (mul_pos (by norm_num) ha)).1 hs
  have has : (3 / 2 : ℝ) ≤ a * s := by nlinarith [Real.pi_gt_d2]
  have hasSq := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3 / 2) has 2
  norm_num at hasSq
  have hprod := mul_le_mul (show (3 / 4 : ℝ) ≤ 1 - a ^ 2 by linarith) hasSq
    (by norm_num : (0 : ℝ) ≤ 9 / 4) (by linarith : 0 ≤ 1 - a ^ 2)
  have hscale : (1 / a) ^ 2 ≤ (1 - a ^ 2) * s ^ 2 := by
    apply (mul_le_mul_right (pow_pos ha 2)).mp
    have hid : (1 / a) ^ 2 * a ^ 2 = 1 := by field_simp
    rw [hid]
    nlinarith only [hprod]
  unfold gaussian
  apply Real.exp_le_exp.mpr
  nlinarith only [hscale]

lemma abs_upperKernel_le_two {ξ u : ℝ} (hu : 1 / Real.pi ≤ u) (hu1 : u < 1) :
    |upperKernel ξ u| ≤ 2 := by
  have hu0 : 0 < u := (one_div_pos.mpr Real.pi_pos).trans_le hu
  have hy : 1 ≤ Real.pi * u := by
    have h := (div_le_iff₀ Real.pi_pos).1 hu
    simpa [mul_comm] using h
  have hrec : 1 / (Real.pi * u) ≤ 1 := (div_le_one (mul_pos Real.pi_pos hu0)).2 hy
  linarith [abs_upperKernel_le (ξ := ξ) hu0 hu1]

lemma gaussianKernelUnit_tail_abs {a x u : ℝ} (ha : 0 < a)
    (hu : 1 / Real.pi ≤ u) (hu1 : u < 1) :
    |gaussianKernelUnit a x u| ≤ 2 * gaussian (1 / a) := by
  have hK := abs_upperKernel_le_two (ξ := x / a) hu hu1
  have ht : 1 / a ≤ Real.pi * u / a := by
    apply div_le_div_of_nonneg_right _ ha.le
    have h := (div_le_iff₀ Real.pi_pos).1 hu
    simpa [mul_comm] using h
  have hg := gaussian_le_inv_scale ha ht
  unfold gaussianKernelUnit
  rw [abs_mul, abs_of_pos (gaussian_pos _)]
  exact mul_le_mul hK hg (gaussian_nonneg _) (by norm_num)

lemma abs_lowerEnvelope_middle {a u : ℝ} (ha : 0 < a) (ha2 : a ≤ 1 / 2)
    (hu : 1 / Real.pi ≤ u) (huθ : u ≤ crossoverRoot / Real.pi) :
    |lowerEnvelope a crossoverRoot (Real.pi * u / a)| ≤ gaussian (1 / a) := by
  have hu0 : 0 < u := (one_div_pos.mpr Real.pi_pos).trans_le hu
  have ht0 : 0 ≤ Real.pi * u / a := by positivity
  have ht : 1 / a ≤ Real.pi * u / a := by
    apply div_le_div_of_nonneg_right _ ha.le
    have h := (div_le_iff₀ Real.pi_pos).1 hu
    simpa [mul_comm] using h
  have hphase : a * (Real.pi * u / a) = Real.pi * u := by field_simp [ha.ne']
  have hroot : a * (Real.pi * u / a) ≤ crossoverRoot := by
    rw [hphase]
    have h := (le_div_iff₀ Real.pi_pos).1 huθ
    simpa [mul_comm] using h
  by_cases hh : a * (Real.pi * u / a) ≤ Real.pi / 2
  · rw [lowerEnvelope, if_pos hh]
    have hc : 0 ≤ Real.cos (a * (Real.pi * u / a)) :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [mul_nonneg ha.le ht0, Real.pi_pos], hh⟩
    rw [abs_of_nonneg (Real.rpow_nonneg hc _)]
    have hp := ZoneA.cosine_profile_le_quartic ha ht0 hh
    rw [abs_of_nonneg hc] at hp
    have hgp : Real.exp (-((Real.pi * u / a) ^ 2 / 2) -
        a ^ 2 * (Real.pi * u / a) ^ 4 / 12) ≤ gaussian (Real.pi * u / a) := by
      unfold gaussian
      apply Real.exp_le_exp.mpr
      have hn : 0 ≤ a ^ 2 * (Real.pi * u / a) ^ 4 / 12 := by positivity
      linarith only [hn]
    exact hp.trans (hgp.trans (gaussian_le_inv_scale ha ht))
  · rw [lowerEnvelope, if_neg hh, if_pos hroot, abs_neg, abs_mul,
      abs_abs, abs_of_pos (Real.exp_pos _)]
    have hs : Real.pi / (2 * a) ≤ Real.pi * u / a := by
      apply (div_le_iff₀ (mul_pos (by norm_num) ha)).2
      have hnot : Real.pi / 2 < a * (Real.pi * u / a) := lt_of_not_ge hh
      nlinarith only [hnot]
    exact (mul_le_of_le_one_left (Real.exp_pos _).le (Real.abs_cos_le_one _)).trans
      (slow_gaussian_le_inv_scale ha ha2 hs)

lemma envelopeDifference_middle_le {a x u : ℝ} (ha : 0 < a) (ha2 : a ≤ 1 / 2)
    (hu : 1 / Real.pi ≤ u) (huθ : u ≤ crossoverRoot / Real.pi) (hu1 : u < 1) :
    envelopeDifference a x u ≤ 4 * gaussian (1 / a) := by
  have hK := abs_upperKernel_le_two (ξ := x / a) hu hu1
  have hL := abs_lowerEnvelope_middle ha ha2 hu huθ
  have hG := gaussianKernelUnit_tail_abs (x := x) ha hu hu1
  have hroot : a * (Real.pi * u / a) ≤ crossoverRoot := by
    have he : a * (Real.pi * u / a) = Real.pi * u := by field_simp [ha.ne']
    rw [he]
    have h := (le_div_iff₀ Real.pi_pos).1 huθ
    simpa [mul_comm] using h
  have hprod : upperKernel (x / a) u * lowerEnvelope a crossoverRoot (Real.pi * u / a) ≤
      2 * gaussian (1 / a) := by
    calc
      _ ≤ |upperKernel (x / a) u * lowerEnvelope a crossoverRoot (Real.pi * u / a)| := le_abs_self _
      _ = |upperKernel (x / a) u| * |lowerEnvelope a crossoverRoot (Real.pi * u / a)| := abs_mul _ _
      _ ≤ _ := mul_le_mul hK hL (abs_nonneg _) (by norm_num)
  have hmax : upperEnvelopeIntegrand a x u ≤ 2 * gaussian (1 / a) := by
    unfold upperEnvelopeIntegrand
    rw [upperEnvelope, if_pos hroot]
    apply max_le hprod
    exact (le_abs_self _).trans hG
  unfold envelopeDifference
  linarith only [hmax, (abs_le.mp hG).1]

lemma envelopeDifference_alias_le {a x u : ℝ} (ha : 0 < a)
    (huθ : crossoverRoot / Real.pi < u) (hu1 : u < 1) :
    envelopeDifference a x u ≤ aliasKernelUnit a x u + 2 * gaussian (1 / a) := by
  have hθpos : 1 < crossoverRoot := by linarith [crossoverRoot_spec.1, Real.pi_gt_d2]
  have hθ : 1 / Real.pi < crossoverRoot / Real.pi :=
    div_lt_div_of_pos_right hθpos Real.pi_pos
  have hu : 1 / Real.pi ≤ u := (hθ.trans huθ).le
  have hG := gaussianKernelUnit_tail_abs (x := x) ha hu hu1
  have hphase : a * (Real.pi * u / a) = Real.pi * u := by field_simp [ha.ne']
  have hroot : ¬a * (Real.pi * u / a) ≤ crossoverRoot := by
    rw [hphase]
    have h := (div_lt_iff₀ Real.pi_pos).1 huθ
    nlinarith only [h]
  have hhalf : ¬a * (Real.pi * u / a) ≤ Real.pi / 2 := by
    intro h
    exact hroot (h.trans crossoverRoot_spec.1.le)
  have hπ : a * (Real.pi * u / a) ≤ Real.pi := by
    rw [hphase]
    nlinarith [Real.pi_pos]
  have he : upperEnvelopeIntegrand a x u = aliasKernelUnit a x u := by
    unfold upperEnvelopeIntegrand lowerEnvelope upperEnvelope
    rw [if_neg hhalf, if_neg hroot, if_pos hπ, if_neg hroot, if_pos hπ]
    exact max_kernel_symmetric _ _ (Real.rpow_nonneg (abs_nonneg _) _)
  unfold envelopeDifference
  rw [he]
  linarith only [(abs_le.mp hG).1]

end KellerKlein
