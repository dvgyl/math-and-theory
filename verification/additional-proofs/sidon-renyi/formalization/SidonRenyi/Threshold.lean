import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.Slope
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

namespace SidonRenyi

open Set Real

noncomputable def thresholdGap (a : ℝ) : ℝ := (2 : ℝ) ^ (a - 1) - (2 * a - 1)

theorem continuous_thresholdGap : Continuous thresholdGap := by
  unfold thresholdGap
  exact ((Real.continuous_const_rpow (by norm_num : (2 : ℝ) ≠ 0)).comp
    (continuous_id.sub continuous_const)).sub
      ((continuous_const.mul continuous_id).sub continuous_const)

theorem strictConvex_thresholdGap : StrictConvexOn ℝ univ thresholdGap := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy hxy p q hp hq hpq
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hne : Real.log 2 * (x - 1) ≠ Real.log 2 * (y - 1) := by
    intro hh
    apply hxy
    have hcancel := mul_left_cancel₀ (ne_of_gt hl) hh
    linarith
  have hh := strictConvexOn_exp.2 (mem_univ (Real.log 2 * (x - 1)))
    (mem_univ (Real.log 2 * (y - 1))) hne hp hq hpq
  simp only [smul_eq_mul] at hh ⊢
  unfold thresholdGap
  simp only [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  have harg : Real.log 2 * (p * x + q * y - 1) =
      p * (Real.log 2 * (x - 1)) + q * (Real.log 2 * (y - 1)) := by
    nlinarith [congrArg (fun z : ℝ => Real.log 2 * z) hpq]
  have hlin : 2 * (p * x + q * y) - 1 = p * (2 * x - 1) + q * (2 * y - 1) := by
    nlinarith
  rw [harg, hlin]
  nlinarith

@[simp] theorem thresholdGap_one : thresholdGap 1 = 0 := by
  norm_num [thresholdGap]

@[simp] theorem thresholdGap_three : thresholdGap 3 = -1 := by
  norm_num [thresholdGap, Real.rpow_two]

@[simp] theorem thresholdGap_four : thresholdGap 4 = 1 := by
  norm_num [thresholdGap, ← Real.rpow_natCast]

/-- The nontrivial crossing lies strictly between three and four. -/
theorem exists_criticalOrder_between : ∃ r : ℝ, 3 < r ∧ r < 4 ∧ thresholdGap r = 0 := by
  have hh : (0 : ℝ) ∈ Icc (thresholdGap 3) (thresholdGap 4) := by
    norm_num
  obtain ⟨r, hr, hz⟩ := intermediate_value_Icc (by norm_num : (3 : ℝ) ≤ 4)
    continuous_thresholdGap.continuousOn hh
  refine ⟨r, ?_, ?_, hz⟩
  · by_contra hn
    have heq : r = 3 := le_antisymm (by linarith) hr.1
    subst r
    norm_num at hz
  · by_contra hn
    have heq : r = 4 := le_antisymm hr.2 (by linarith)
    subst r
    norm_num at hz

theorem thresholdGap_neg_between {r a : ℝ} (_hr : 1 < r)
    (hz : thresholdGap r = 0) (ha : 1 < a) (har : a < r) : thresholdGap a < 0 := by
  have hh := strictConvex_thresholdGap.slope_strict_mono_adjacent
    (mem_univ (1 : ℝ)) (mem_univ r) ha har
  rw [thresholdGap_one, hz] at hh
  have hm := (div_lt_div_iff₀ (by linarith : 0 < a - 1) (by linarith : 0 < r - a)).mp hh
  have hf : thresholdGap a * (r - 1) < 0 := by nlinarith
  by_contra hn
  have hh := mul_nonneg (le_of_not_gt hn) (by linarith : 0 ≤ r - 1)
  linarith

theorem thresholdGap_pos_above {r a : ℝ} (hr : 1 < r)
    (hz : thresholdGap r = 0) (hra : r < a) : 0 < thresholdGap a := by
  have hh := strictConvex_thresholdGap.slope_strict_mono_adjacent
    (mem_univ (1 : ℝ)) (mem_univ a) hr hra
  rw [thresholdGap_one, hz] at hh
  simp only [sub_zero, sub_self, zero_div] at hh
  exact (div_pos_iff_of_pos_right (sub_pos.mpr hra)).mp hh

/-- The equation identifies the entire valid order interval, with no numerical assumption. -/
theorem threshold_condition_iff {r a : ℝ} (hr : 1 < r) (hz : thresholdGap r = 0)
    (ha : 1 < a) : (2 : ℝ) ^ (a - 1) ≤ 2 * a - 1 ↔ a ≤ r := by
  have heq : (2 : ℝ) ^ (a - 1) ≤ 2 * a - 1 ↔ thresholdGap a ≤ 0 := by
    unfold thresholdGap
    constructor <;> intro h <;> linarith
  rw [heq]
  rcases lt_trichotomy a r with har | heq | hra
  · have hn := thresholdGap_neg_between hr hz ha har
    constructor <;> intro h <;> linarith
  · subst a
    rw [hz]
    simp
  · have hp := thresholdGap_pos_above hr hz hra
    constructor <;> intro h <;> linarith

theorem criticalOrder_unique {r s : ℝ} (hr : 1 < r) (hs : 1 < s)
    (hzr : thresholdGap r = 0) (hzs : thresholdGap s = 0) : r = s := by
  rcases lt_trichotomy r s with h | h | h
  · have := thresholdGap_neg_between hs hzs hr h
    linarith
  · exact h
  · have := thresholdGap_neg_between hr hzr hs h
    linarith

/-- The unique critical order greater than one. -/
noncomputable def criticalOrder : ℝ := Classical.choose exists_criticalOrder_between

theorem criticalOrder_bounds : 3 < criticalOrder ∧ criticalOrder < 4 := by
  have h := Classical.choose_spec exists_criticalOrder_between
  exact ⟨h.1, h.2.1⟩

theorem criticalOrder_gt_one : 1 < criticalOrder := by
  linarith [criticalOrder_bounds.1]

@[simp] theorem thresholdGap_criticalOrder : thresholdGap criticalOrder = 0 :=
  (Classical.choose_spec exists_criticalOrder_between).2.2

theorem criticalOrder_equation :
    (2 : ℝ) ^ (criticalOrder - 1) = 2 * criticalOrder - 1 := by
  have h := thresholdGap_criticalOrder
  unfold thresholdGap at h
  linarith

theorem criticalOrder_condition_iff {a : ℝ} (ha : 1 < a) :
    (2 : ℝ) ^ (a - 1) ≤ 2 * a - 1 ↔ a ≤ criticalOrder :=
  threshold_condition_iff criticalOrder_gt_one thresholdGap_criticalOrder ha

theorem criticalOrder_strict_condition_iff {a : ℝ} (ha : 1 < a) :
    2 * a - 1 < (2 : ℝ) ^ (a - 1) ↔ criticalOrder < a := by
  simpa only [not_le] using not_congr (criticalOrder_condition_iff ha)

theorem exists_unique_criticalOrder :
    ∃! a : ℝ, 1 < a ∧ (2 : ℝ) ^ (a - 1) = 2 * a - 1 := by
  refine ⟨criticalOrder, ⟨criticalOrder_gt_one, criticalOrder_equation⟩, ?_⟩
  intro a ha
  apply criticalOrder_unique ha.1 criticalOrder_gt_one
  · unfold thresholdGap
    rw [ha.2]
    ring
  · exact thresholdGap_criticalOrder

end SidonRenyi
