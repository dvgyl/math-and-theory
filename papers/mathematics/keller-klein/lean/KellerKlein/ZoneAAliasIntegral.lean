import KellerKlein.ZoneAAlias
import KellerKlein.ShiftedGaussianMoments

noncomputable section
open Set MeasureTheory

namespace KellerKlein.ZoneA

def aliasValue (a ξ c : ℝ) : ℝ :=
  a ^ 2 / Real.pi ^ 2 * Real.cos (Real.pi * ξ) * shiftedGaussianMoment 1 c +
  a ^ 3 / Real.pi ^ 2 * (ξ + 1 / 3) * Real.sin (Real.pi * ξ) * shiftedGaussianMoment 2 c +
  a ^ 5 / Real.pi ^ 5 * Real.sin (Real.pi * ξ) * shiftedGaussianMoment 4 c

def aliasHigh (a ξ : ℝ) : ℝ :=
  a ^ 2 * Real.cos (Real.pi * ξ) / Real.pi ^ 2 +
  phi0 * a ^ 3 * (ξ + 1 / 3) * Real.sin (Real.pi * ξ) / Real.pi +
  3 * phi0 * a ^ 5 * Real.sin (Real.pi * ξ) / Real.pi ^ 4

lemma alias_integrand_eq (a ξ c v : ℝ) :
    aliasPolynomial ξ (a * v / Real.pi) * gaussian (v + c) =
      (a / Real.pi * Real.cos (Real.pi * ξ)) * (v ^ 1 * gaussian (v + c)) +
      ((Real.pi * ξ + Real.pi / 3) * a ^ 2 / Real.pi ^ 2 * Real.sin (Real.pi * ξ)) *
        (v ^ 2 * gaussian (v + c)) +
      (a ^ 4 / Real.pi ^ 4 * Real.sin (Real.pi * ξ)) * (v ^ 4 * gaussian (v + c)) := by
  unfold aliasPolynomial
  ring

lemma integrableOn_aliasPolynomial (a ξ : ℝ) {c : ℝ} (hc : 0 ≤ c) :
    IntegrableOn (fun v => aliasPolynomial ξ (a * v / Real.pi) * gaussian (v + c)) (Ioi 0) := by
  have h1 := (integrableOn_shiftedGaussianMoment 1 hc).const_mul
    (a / Real.pi * Real.cos (Real.pi * ξ))
  have h2 := (integrableOn_shiftedGaussianMoment 2 hc).const_mul
    ((Real.pi * ξ + Real.pi / 3) * a ^ 2 / Real.pi ^ 2 * Real.sin (Real.pi * ξ))
  have h4 := (integrableOn_shiftedGaussianMoment 4 hc).const_mul
    (a ^ 4 / Real.pi ^ 4 * Real.sin (Real.pi * ξ))
  simp_rw [alias_integrand_eq]
  exact (h1.add h2).add h4

lemma integral_aliasPolynomial_eq (a ξ : ℝ) {c : ℝ} (hc : 0 ≤ c) :
    a / Real.pi * (∫ v in Ioi (0 : ℝ),
      aliasPolynomial ξ (a * v / Real.pi) * gaussian (v + c)) = aliasValue a ξ c := by
  simp_rw [alias_integrand_eq]
  rw [integral_add, integral_add, integral_const_mul, integral_const_mul, integral_const_mul]
  · unfold aliasValue shiftedGaussianMoment
    field_simp [Real.pi_ne_zero]
    ring
  · exact (integrableOn_shiftedGaussianMoment 1 hc).const_mul _
  · exact (integrableOn_shiftedGaussianMoment 2 hc).const_mul _
  · exact ((integrableOn_shiftedGaussianMoment 1 hc).const_mul _).add
      ((integrableOn_shiftedGaussianMoment 2 hc).const_mul _)
  · exact (integrableOn_shiftedGaussianMoment 4 hc).const_mul _

lemma aliasValue_le_high {a ξ c : ℝ} (ha : 0 ≤ a) (hξ : 0 ≤ ξ)
    (hξ1 : ξ ≤ 1 / 2) (hc : 0 ≤ c) : aliasValue a ξ c ≤ aliasHigh a ξ := by
  have hβ : 0 ≤ Real.pi * ξ := mul_nonneg Real.pi_pos.le hξ
  have hβ1 : Real.pi * ξ ≤ Real.pi / 2 := by nlinarith [Real.pi_pos]
  have hcos : 0 ≤ Real.cos (Real.pi * ξ) := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [Real.pi_pos], hβ1⟩
  have hsin : 0 ≤ Real.sin (Real.pi * ξ) := Real.sin_nonneg_of_nonneg_of_le_pi
    hβ (by linarith [Real.pi_pos])
  have h1 := mul_le_mul_of_nonneg_left (shiftedGaussianMoment_le_halfMoment 1 hc)
    (by positivity : 0 ≤ a ^ 2 / Real.pi ^ 2 * Real.cos (Real.pi * ξ))
  have h2 := mul_le_mul_of_nonneg_left (shiftedGaussianMoment_le_halfMoment 2 hc)
    (by positivity : 0 ≤ a ^ 3 / Real.pi ^ 2 * (ξ + 1 / 3) * Real.sin (Real.pi * ξ))
  have h4 := mul_le_mul_of_nonneg_left (shiftedGaussianMoment_le_halfMoment 4 hc)
    (by positivity : 0 ≤ a ^ 5 / Real.pi ^ 5 * Real.sin (Real.pi * ξ))
  rw [halfMoment_one] at h1
  rw [halfMoment_two] at h2
  rw [halfMoment_four] at h4
  unfold aliasValue aliasHigh
  convert add_le_add (add_le_add h1 h2) h4 using 1
  field_simp [Real.pi_ne_zero]
  ring

lemma aliasValue_le_third_high {a ξ c : ℝ} (ha : 0 ≤ a) (hξ : 0 ≤ ξ)
    (hξ1 : ξ ≤ 1 / 2) (hc : 2 ≤ c) : aliasValue a ξ c ≤ aliasHigh a ξ / 3 := by
  have hβ : 0 ≤ Real.pi * ξ := mul_nonneg Real.pi_pos.le hξ
  have hβ1 : Real.pi * ξ ≤ Real.pi / 2 := by nlinarith [Real.pi_pos]
  have hcos : 0 ≤ Real.cos (Real.pi * ξ) := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [Real.pi_pos], hβ1⟩
  have hsin : 0 ≤ Real.sin (Real.pi * ξ) := Real.sin_nonneg_of_nonneg_of_le_pi
    hβ (by linarith [Real.pi_pos])
  have h1 := mul_le_mul_of_nonneg_left (shiftedGaussianMoment_le_third 1 hc)
    (by positivity : 0 ≤ a ^ 2 / Real.pi ^ 2 * Real.cos (Real.pi * ξ))
  have h2 := mul_le_mul_of_nonneg_left (shiftedGaussianMoment_le_third 2 hc)
    (by positivity : 0 ≤ a ^ 3 / Real.pi ^ 2 * (ξ + 1 / 3) * Real.sin (Real.pi * ξ))
  have h4 := mul_le_mul_of_nonneg_left (shiftedGaussianMoment_le_third 4 hc)
    (by positivity : 0 ≤ a ^ 5 / Real.pi ^ 5 * Real.sin (Real.pi * ξ))
  rw [halfMoment_one] at h1
  rw [halfMoment_two] at h2
  rw [halfMoment_four] at h4
  unfold aliasValue aliasHigh
  convert add_le_add (add_le_add h1 h2) h4 using 1
  field_simp [Real.pi_ne_zero]
  ring

lemma alias_truncated_integral_bound {a ξ c L : ℝ} (ha : 0 ≤ a) (hξ : 0 ≤ ξ)
    (hξ1 : ξ ≤ 1 / 2) (hc : 0 ≤ c) :
    a / Real.pi * (∫ v in Ioc (0 : ℝ) L,
      aliasPolynomial ξ (a * v / Real.pi) * gaussian (v + c)) ≤ aliasValue a ξ c := by
  rw [← integral_aliasPolynomial_eq a ξ hc]
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ a / Real.pi)
  apply setIntegral_mono_set (integrableOn_aliasPolynomial a ξ hc)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    exact mul_nonneg (aliasPolynomial_nonneg hξ hξ1
      (div_nonneg (mul_nonneg ha hv.le) Real.pi_pos.le)) (gaussian_nonneg _)
  · exact Filter.Eventually.of_forall fun v hv => hv.1

end KellerKlein.ZoneA
