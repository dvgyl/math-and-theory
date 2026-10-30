import KellerKlein.ZoneAIntegralBound
import KellerKlein.ZoneAFinalAlgebra

/-!
# The actual Zone A Hölder-profile inequality

This module closes the analytic estimate for all normalized locations
`0 ≤ ξ ≤ 1/2`, all maximal coefficients `0 < a ≤ 7/100`, and every
Hölder profile parameter `0 < b ≤ a`.  The theorem concerns the genuine
Prawitz-kernel integral.  No analytic estimate is assumed as an axiom or
as a hypothesis of the main theorem.
-/

noncomputable section

namespace KellerKlein.ZoneA

lemma separation_ge_two {a b : ℝ} (ha : 0 < a) (ha1 : a ≤ 7 / 100)
    (hb : 0 < b) (hba : b ≤ 19 * a / 20) : 2 ≤ separation a b := by
  have hden : 0 < 19 * a / 20 := by positivity
  have hrec : Real.pi / (19 * a / 20) ≤ Real.pi / b :=
    div_le_div_of_nonneg_left Real.pi_pos.le hb hba
  have he : Real.pi / (19 * a / 20) - Real.pi / a = Real.pi / (19 * a) := by
    field_simp [ha.ne']
    ring
  have hc : Real.pi / (19 * a) ≤ separation a b := by
    unfold separation
    rw [← he]
    linarith only [hrec]
  have htwo : (2 : ℝ) ≤ Real.pi / (19 * a) := by
    apply (le_div_iff₀ (by positivity : 0 < 19 * a)).2
    nlinarith [Real.pi_gt_d2]
  exact htwo.trans hc

theorem holderProfile_le_c_pair {a b ξ : ℝ} (ha : 0 < a) (ha1 : a ≤ 7 / 100)
    (hb : 0 < b) (hba : b ≤ a) (hξ : 0 ≤ ξ) (hξ1 : ξ ≤ 1 / 2) :
    holderProfile a b ξ ≤ c a + c (ξ * a) := by
  have haOne : a ≤ 1 := by linarith
  have hθ0 : 0 ≤ b / a := div_nonneg hb.le ha.le
  have hθ1 : b / a ≤ 1 := (div_le_one ha).2 hba
  have hc0 := separation_nonneg ha hb hba
  have htarget := targetLower_le_c_pair ha.le hξ
  by_cases hθ : 19 / 20 ≤ b / a
  · have hprofile := holderProfile_le_primary_alias ha haOne hb hba hξ hξ1
    have halias := aliasValue_le_high ha.le hξ hξ1 hc0
    have halgebra := high_algebra_margin ha.le ha1 hθ hθ1 hξ hξ1
    rw [div_mul_cancel₀ b ha.ne'] at halgebra
    have hgap : 0 ≤ a ^ 3 / 200 := by positivity
    linarith only [hprofile, halias, halgebra, htarget, hgap]
  · have hba95 : b ≤ 19 * a / 20 := by
      have h := (div_le_iff₀ ha).1 (lt_of_not_ge hθ).le
      nlinarith only [h]
    have hc2 := separation_ge_two ha ha1 hb hba95
    have hprofile := holderProfile_le_gaussian_alias ha haOne hb hba hξ hξ1
    have halias := aliasValue_le_third_high ha.le hξ hξ1 hc2
    have halgebra := low_algebra_margin ha.le ha1 hξ hξ1
    have hgap : 0 ≤ a ^ 2 / 20 := by positivity
    linarith only [hprofile, halias, halgebra, htarget, hgap]

end KellerKlein.ZoneA
