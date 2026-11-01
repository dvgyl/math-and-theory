import KellerKlein.ZoneAAliasScaled
import KellerKlein.ZoneATailBound

noncomputable section
open Set MeasureTheory

namespace KellerKlein.ZoneA

def cutoff (a b : ℝ) : ℝ := min (Real.pi / (2 * b)) (Real.pi / a)

lemma cutoff_nonneg {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : 0 ≤ cutoff a b := by
  unfold cutoff
  positivity

lemma cutoff_le_a (a b : ℝ) : cutoff a b ≤ Real.pi / a := min_le_right _ _
lemma cutoff_le_b (a b : ℝ) : cutoff a b ≤ Real.pi / (2 * b) := min_le_left _ _

lemma cutoff_lower {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hba : b ≤ a) :
    1 / a ≤ cutoff a b := by
  apply le_min
  · apply (div_le_div_iff₀ ha (mul_pos (by norm_num) hb)).2
    have hp : (2 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d2]
    have hpa := mul_le_mul_of_nonneg_right hp ha.le
    nlinarith only [hpa, hba]
  · exact div_le_div_of_nonneg_right (by linarith [Real.pi_gt_d2] : (1 : ℝ) ≤ Real.pi) ha.le

lemma holderProfile_split {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (ξ : ℝ) :
    holderProfile a b ξ =
      a / Real.pi * (∫ s in (0 : ℝ)..(cutoff a b), scaledProfile a b ξ s) +
      a / Real.pi * (∫ s in (cutoff a b)..(Real.pi / a), scaledProfile a b ξ s) := by
  rw [holderProfile_eq_scaled ha.ne']
  have h0 := intervalIntegrable_scaledProfile_subinterval ha b ξ le_rfl
    (cutoff_nonneg ha hb) (cutoff_le_a a b)
  have h1 := intervalIntegrable_scaledProfile_subinterval ha b ξ
    (cutoff_nonneg ha hb) (cutoff_le_a a b) le_rfl
  rw [← intervalIntegral.integral_add_adjacent_intervals h0 h1, mul_add]

lemma aliasValue_nonneg {a ξ c : ℝ} (ha : 0 ≤ a) (hξ : 0 ≤ ξ) (hξ1 : ξ ≤ 1 / 2) :
    0 ≤ aliasValue a ξ c := by
  have hβ : 0 ≤ Real.pi * ξ := mul_nonneg Real.pi_pos.le hξ
  have hβ1 : Real.pi * ξ ≤ Real.pi / 2 := by nlinarith [Real.pi_pos]
  have hcos : 0 ≤ Real.cos (Real.pi * ξ) := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [Real.pi_pos], hβ1⟩
  have hsin : 0 ≤ Real.sin (Real.pi * ξ) := Real.sin_nonneg_of_nonneg_of_le_pi
    hβ (by linarith [Real.pi_pos])
  have h1 := shiftedGaussianMoment_nonneg 1 c
  have h2 := shiftedGaussianMoment_nonneg 2 c
  have h4 := shiftedGaussianMoment_nonneg 4 c
  unfold aliasValue
  positivity

lemma scaled_remaining_alias_bound {a b ξ : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hba : b ≤ a) (hξ : 0 ≤ ξ) (hξ1 : ξ ≤ 1 / 2) :
    a / Real.pi * (∫ s in (cutoff a b)..(Real.pi / a), scaledProfile a b ξ s) ≤
      aliasValue a ξ (separation a b) := by
  by_cases hhalf : a ≤ 2 * b
  · have hS : Real.pi / (2 * b) ≤ Real.pi / a :=
      div_le_div_of_nonneg_left Real.pi_pos.le ha hhalf
    rw [cutoff, min_eq_left hS]
    exact scaled_alias_integral_bound ha hb hba hhalf hξ hξ1
  · have hS : Real.pi / a ≤ Real.pi / (2 * b) :=
      div_le_div_of_nonneg_left Real.pi_pos.le (mul_pos (by norm_num) hb) (le_of_not_ge hhalf)
    rw [cutoff, min_eq_right hS, intervalIntegral.integral_same, mul_zero]
    exact aliasValue_nonneg ha.le hξ hξ1

lemma holderProfile_le_primary_alias {a b ξ : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hb : 0 < b) (hba : b ≤ a) (hξ : 0 ≤ ξ) (hξ1 : ξ ≤ 1 / 2) :
    holderProfile a b ξ ≤ primaryValue a b ξ + 128 * a ^ 8 +
      aliasValue a ξ (separation a b) := by
  have hprimary := (scaled_primary_bound ha hb hξ hξ1 (cutoff_nonneg ha hb)
    (cutoff_le_a a b) (cutoff_le_b a b)).trans
    (primary_truncated_integral_bound ha ha1 hb.le hba hξ hξ1 (cutoff_lower ha hb hba))
  rw [holderProfile_split ha hb ξ]
  exact add_le_add hprimary (scaled_remaining_alias_bound ha hb hba hξ hξ1)

lemma holderProfile_le_gaussian_alias {a b ξ : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hb : 0 < b) (hba : b ≤ a) (hξ : 0 ≤ ξ) (hξ1 : ξ ≤ 1 / 2) :
    holderProfile a b ξ ≤ primaryValue a 0 ξ + 128 * a ^ 8 +
      aliasValue a ξ (separation a b) := by
  have hprimary := (scaled_primary_gaussian_bound ha hb hξ hξ1 (cutoff_nonneg ha hb)
    (cutoff_le_a a b) (cutoff_le_b a b)).trans
    (primary_truncated_integral_bound ha ha1 le_rfl ha.le hξ hξ1 (cutoff_lower ha hb hba))
  rw [holderProfile_split ha hb ξ]
  exact add_le_add hprimary (scaled_remaining_alias_bound ha hb hba hξ hξ1)

end KellerKlein.ZoneA
