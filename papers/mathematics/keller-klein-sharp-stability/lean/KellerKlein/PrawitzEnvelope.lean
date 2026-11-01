import KellerKlein.PrawitzFinite
import KellerKlein.EnvelopeIntegral
import KellerKlein.ProfileMixture
import KellerKlein.ZoneATheorem

open MeasureTheory Set
open scoped BigOperators

namespace KellerKlein

lemma continuous_cosProduct {ι : Type*} (S : Finset ι) (c : ι → ℝ) :
    Continuous (cosProduct S c) := by
  unfold cosProduct
  fun_prop

lemma mul_le_max_envelopes {l p u k : ℝ} (hl : l ≤ p) (hu : p ≤ u) :
    k * p ≤ max (k * l) (k * u) := by
  rcases le_total 0 k with hk | hk
  · exact (mul_le_mul_of_nonneg_left hu hk).trans (le_max_right _ _)
  · exact (mul_le_mul_of_nonpos_left hl hk).trans (le_max_left _ _)

/-- The actual finite Rademacher law is bounded by the exact envelope integral. -/
theorem rademacher_concentration_le_JUpper {n : ℕ} (coeff : Fin n → ℝ)
    {a x : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hc : ∀ i, 0 ≤ coeff i)
    (hca : ∀ i, coeff i ≤ a) (hvar : ∑ i, coeff i ^ 2 = 1) (hx : 0 ≤ x) :
    rademacherConcentration coeff x ≤ 2 * JUpper a x := by
  have hp := rademacher_concentration_le_prawitz coeff hx
    (show 0 < Real.pi / a by positivity)
  have heq : (fun u : ℝ => symmetricPrawitzKernel x (Real.pi / a) u *
      cosProduct Finset.univ coeff (Real.pi / a * u)) =
      (fun u => upperKernel (x / a) u * cosProduct Finset.univ coeff (Real.pi * u / a)) := by
    funext u
    rw [symmetricPrawitzKernel_eq_upperKernel ha.ne']
    congr 2
    ring
  rw [heq] at hp
  have hi : IntervalIntegrable
      (fun u => upperKernel (x / a) u * cosProduct Finset.univ coeff (Real.pi * u / a))
      volume 0 1 := by
    apply (intervalIntegrable_upperKernel (x / a)).mul_continuousOn
    exact ((continuous_cosProduct Finset.univ coeff).comp
      ((continuous_const.mul continuous_id).div_const a)).continuousOn
  have hb : (∫ u in (0 : ℝ)..1,
      upperKernel (x / a) u * cosProduct Finset.univ coeff (Real.pi * u / a)) ≤ JUpper a x := by
    apply intervalIntegral.integral_mono_on (by norm_num) hi
      (intervalIntegrable_upperEnvelopeIntegrand ha ha1)
    intro u hu
    have ht : 0 ≤ Real.pi * u / a := div_nonneg (mul_nonneg Real.pi_pos.le hu.1) ha.le
    have he := actual_characteristic_envelopes Finset.univ coeff ha
      (fun i _ => hc i) (fun i _ => hca i) hvar ht
    exact mul_le_max_envelopes he.1 he.2
  linarith

lemma upperKernel_nonneg_closed {ξ : ℝ} (hξ : 0 ≤ ξ) (hξ1 : ξ ≤ 1 / 2) :
    ∀ u ∈ Icc (0 : ℝ) 1, 0 ≤ upperKernel ξ u := by
  intro u hu
  rcases eq_or_lt_of_le hu.1 with rfl | hu0
  · simp [upperKernel]
  rcases lt_or_eq_of_le hu.2 with hu1 | rfl
  · exact upperKernel_nonneg hξ hξ1 hu0 hu1
  · have hs : 0 ≤ Real.sin (Real.pi * ξ) := Real.sin_nonneg_of_nonneg_of_le_pi
      (mul_nonneg Real.pi_pos.le hξ) (by nlinarith [Real.pi_pos])
    simpa [upperKernel, rho] using
      mul_nonneg (one_div_nonneg.mpr Real.pi_pos.le) hs

/-- The complete small-location probability inequality. Every analytic input
in the scalar profile theorem and in Prawitz has been discharged. -/
theorem rademacher_concentration_zoneA {n : ℕ} (coeff : Fin n → ℝ)
    {a x : ℝ} (ha : 0 < a) (ha7 : a ≤ 7 / 100) (hc : ∀ i, 0 ≤ coeff i)
    (hca : ∀ i, coeff i ≤ a) (hvar : ∑ i, coeff i ^ 2 = 1)
    (hx : 0 ≤ x) (hxa : x ≤ a / 2) :
    rademacherConcentration coeff x ≤ H a + H x := by
  have hξ : 0 ≤ x / a := div_nonneg hx ha.le
  have hξ1 : x / a ≤ (1 / 2 : ℝ) := (div_le_iff₀ ha).mpr (by linarith)
  have hfreq (u : ℝ) : Real.pi / a * u = Real.pi * u / a := by ring
  have hi : IntervalIntegrable
      (fun u => upperKernel (x / a) u * cosProduct Finset.univ coeff (Real.pi / a * u))
      volume 0 1 := by
    apply (intervalIntegrable_upperKernel (x / a)).mul_continuousOn
    exact ((continuous_cosProduct Finset.univ coeff).comp
      (continuous_const.mul continuous_id)).continuousOn
  have hprofiles : ∀ i ∈ (Finset.univ : Finset (Fin n)), IntervalIntegrable
      (fun u => upperKernel (x / a) u * cosineProfile (coeff i) (Real.pi / a * u))
      volume 0 1 := by
    intro i hi
    simpa only [hfreq] using intervalIntegrable_upperKernel_cosineProfile a (coeff i) (x / a)
  have hbounds : ∀ i ∈ (Finset.univ : Finset (Fin n)), coeff i ≠ 0 →
      (∫ u in (0 : ℝ)..1, upperKernel (x / a) u * cosineProfile (coeff i) (Real.pi / a * u)) ≤
        c a + c x := by
    intro i hi hnz
    have hci : 0 < coeff i := lt_of_le_of_ne (hc i) (Ne.symm hnz)
    have h := ZoneA.holderProfile_le_c_pair ha ha7 hci (hca i) hξ hξ1
    simpa only [ZoneA.holderProfile, hfreq, div_mul_cancel₀ x ha.ne'] using h
  have hb := integral_cosProduct_le_uniform_profile Finset.univ coeff hvar
    (upperKernel (x / a)) (Real.pi / a) (c a + c x)
    (upperKernel_nonneg_closed hξ hξ1) hi hprofiles hbounds
  have hp := rademacher_concentration_le_prawitz coeff hx
    (show 0 < Real.pi / a by positivity)
  have heq : symmetricPrawitzKernel x (Real.pi / a) = upperKernel (x / a) := by
    funext u
    exact symmetricPrawitzKernel_eq_upperKernel ha.ne' x u
  rw [heq] at hp
  unfold H
  linarith

theorem rademacherCDF_zoneA {n : ℕ} (coeff : Fin n → ℝ)
    {a x : ℝ} (ha : 0 < a) (ha7 : a ≤ 7 / 100) (hc : ∀ i, 0 ≤ coeff i)
    (hca : ∀ i, coeff i ≤ a) (hvar : ∑ i, coeff i ^ 2 = 1)
    (hx : 0 ≤ x) (hxa : x ≤ a / 2) :
    rademacherCDF coeff x ≤ 1 / 2 + c x + c a := by
  have hp := rademacher_concentration_zoneA coeff ha ha7 hc hca hvar hx hxa
  have hs := rademacherCDF_symmetry coeff x
  have hc0 := rademacherConcentration_eq_one_sub_two_strictCDF coeff hx
  unfold H at hp
  linarith

end KellerKlein
