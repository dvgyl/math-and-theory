import KellerKlein.GaussianMoments

noncomputable section
open Set MeasureTheory

namespace KellerKlein

def shiftedGaussianMoment (k : ℕ) (c : ℝ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), t ^ k * gaussian (t + c)

lemma gaussian_add_le {t c : ℝ} (ht : 0 ≤ t) (hc : 0 ≤ c) :
    gaussian (t + c) ≤ gaussian c * gaussian t := by
  unfold gaussian
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_nonneg ht hc]

lemma gaussian_add_le_left {t c : ℝ} (ht : 0 ≤ t) (hc : 0 ≤ c) :
    gaussian (t + c) ≤ gaussian t := by
  calc
    gaussian (t + c) ≤ gaussian c * gaussian t := gaussian_add_le ht hc
    _ ≤ 1 * gaussian t := mul_le_mul_of_nonneg_right (gaussian_le_one c) (gaussian_nonneg t)
    _ = gaussian t := one_mul _

lemma integrableOn_shiftedGaussianMoment (k : ℕ) {c : ℝ} (hc : 0 ≤ c) :
    IntegrableOn (fun t => t ^ k * gaussian (t + c)) (Ioi (0 : ℝ)) := by
  have hcont : Continuous (fun t : ℝ => t ^ k * gaussian (t + c)) :=
    (continuous_id.pow k).mul (continuous_gaussian.comp (continuous_id.add continuous_const))
  apply (integrableOn_pow_gaussian k).mono' hcont.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (pow_nonneg ht.le k) (gaussian_nonneg (t + c)))]
  exact mul_le_mul_of_nonneg_left (gaussian_add_le_left ht.le hc) (pow_nonneg ht.le k)

lemma shiftedGaussianMoment_nonneg (k : ℕ) (c : ℝ) :
    0 ≤ shiftedGaussianMoment k c := by
  apply setIntegral_nonneg measurableSet_Ioi
  intro t ht
  exact mul_nonneg (pow_nonneg ht.le k) (gaussian_nonneg (t + c))

lemma shiftedGaussianMoment_le_product (k : ℕ) {c : ℝ} (hc : 0 ≤ c) :
    shiftedGaussianMoment k c ≤ gaussian c * halfMoment k := by
  unfold shiftedGaussianMoment halfMoment
  rw [← integral_const_mul]
  apply setIntegral_mono_on (integrableOn_shiftedGaussianMoment k hc)
    ((integrableOn_pow_gaussian k).const_mul (gaussian c)) measurableSet_Ioi
  intro t ht
  have h := mul_le_mul_of_nonneg_left (gaussian_add_le ht.le hc) (pow_nonneg ht.le k)
  nlinarith only [h]

lemma shiftedGaussianMoment_le_halfMoment (k : ℕ) {c : ℝ} (hc : 0 ≤ c) :
    shiftedGaussianMoment k c ≤ halfMoment k := by
  calc
    shiftedGaussianMoment k c ≤ gaussian c * halfMoment k :=
      shiftedGaussianMoment_le_product k hc
    _ ≤ 1 * halfMoment k := mul_le_mul_of_nonneg_right (gaussian_le_one c) (halfMoment_nonneg k)
    _ = halfMoment k := one_mul _

lemma gaussian_le_third {c : ℝ} (hc : 2 ≤ c) : gaussian c ≤ 1 / 3 := by
  have hsq : 2 ≤ c ^ 2 / 2 := by nlinarith
  have he := Real.add_one_le_exp (c ^ 2 / 2)
  have hp : 0 < Real.exp (c ^ 2 / 2) := Real.exp_pos _
  unfold gaussian
  rw [neg_div, Real.exp_neg, inv_eq_one_div]
  exact (div_le_div_iff₀ hp (by norm_num : (0 : ℝ) < 3)).2 (by linarith)

lemma shiftedGaussianMoment_le_third (k : ℕ) {c : ℝ} (hc : 2 ≤ c) :
    shiftedGaussianMoment k c ≤ halfMoment k / 3 := by
  have hm := shiftedGaussianMoment_le_product k (by linarith : 0 ≤ c)
  have ht := mul_le_mul_of_nonneg_right (gaussian_le_third hc) (halfMoment_nonneg k)
  nlinarith only [hm, ht]

end KellerKlein
