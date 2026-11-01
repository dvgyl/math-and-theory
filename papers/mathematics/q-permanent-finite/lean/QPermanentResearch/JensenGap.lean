import Mathlib.Data.Real.Pi.Bounds
import Mathlib.Tactic

/-!
# Exact scalar constants in the rank-three Jensen argument

This module proves the inequalities involving pi and square roots which enter
the quantified Jensen gain. It does not formalize the probabilistic Jensen
argument, the log-potential concentration, or a matrix counterexample.
-/

namespace QPermanentResearch

theorem sqrt_two_gt_seven_fifths : (7 / 5 : ℝ) < Real.sqrt 2 := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hn := Real.sqrt_nonneg (2 : ℝ)
  nlinarith

theorem sqrt_eighty_five_lt : Real.sqrt 85 < (461 / 50 : ℝ) := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 85 by norm_num)
  have hn := Real.sqrt_nonneg (85 : ℝ)
  nlinarith

theorem inv_sqrt_two_lt : (1 : ℝ) / Real.sqrt 2 < 99 / 140 := by
  have hp : 0 < Real.sqrt (2 : ℝ) := by positivity
  apply (div_lt_iff₀ hp).2
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  nlinarith

theorem pi_lt_twenty_two_sevenths : Real.pi < (22 / 7 : ℝ) := by
  linarith [Real.pi_lt_d4]

noncomputable def jensenEventProbability : ℝ :=
  (7 / Real.sqrt 85 - 1 / Real.sqrt 2) / 2

noncomputable def angularMean : ℝ := 2 * Real.sqrt 2 / Real.pi

noncomputable def angularGini : ℝ :=
  4 * Real.sqrt 2 * (4 - Real.pi) / Real.pi ^ 2

theorem jensenEventProbability_gt :
    (13 / 500 : ℝ) < jensenEventProbability := by
  have h85 : 0 < Real.sqrt (85 : ℝ) := by positivity
  have hfrac : (350 / 461 : ℝ) < 7 / Real.sqrt 85 := by
    apply (lt_div_iff₀ h85).2
    nlinarith [sqrt_eighty_five_lt]
  unfold jensenEventProbability
  linarith [inv_sqrt_two_lt]

theorem angularMean_pos : 0 < angularMean := by
  unfold angularMean
  positivity

theorem angularMean_lt_one : angularMean < 1 := by
  unfold angularMean
  apply (div_lt_iff₀ Real.pi_pos).2
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hn := Real.sqrt_nonneg (2 : ℝ)
  nlinarith [Real.pi_gt_three]

theorem angular_conditional_gain_gt :
    (3 / 16 : ℝ) < angularGini - angularMean / 3 := by
  have hp := Real.pi_pos
  have hp2 : 0 < Real.pi ^ 2 := sq_pos_of_pos hp
  have hs := sqrt_two_gt_seven_fifths
  have hpu := pi_lt_twenty_two_sevenths
  have hlinear : (2 : ℝ) < 24 - 7 * Real.pi := by linarith
  have hnum : (28 / 5 : ℝ) < 2 * Real.sqrt 2 * (24 - 7 * Real.pi) := by
    nlinarith
  have hsq : Real.pi ^ 2 < (22 / 7 : ℝ) ^ 2 := by nlinarith
  have heq : angularGini - angularMean / 3 =
      2 * Real.sqrt 2 * (24 - 7 * Real.pi) / (3 * Real.pi ^ 2) := by
    unfold angularGini angularMean
    field_simp
    ring
  rw [heq]
  apply (lt_div_iff₀ (by positivity : (0 : ℝ) < 3 * Real.pi ^ 2)).2
  nlinarith

theorem jensen_scalar_gain_gt :
    (1 / 8000 : ℝ) <
      jensenEventProbability ^ 2 * (angularGini - angularMean / 3) := by
  have hp := jensenEventProbability_gt
  have hg := angular_conditional_gain_gt
  have hp2 : (13 / 500 : ℝ) ^ 2 < jensenEventProbability ^ 2 := by
    nlinarith
  have hprod : (13 / 500 : ℝ) ^ 2 * (3 / 16) <
      jensenEventProbability ^ 2 * (angularGini - angularMean / 3) := by
    nlinarith
  norm_num at hprod ⊢
  linarith

theorem truncation_twenty_thousand_cost :
    (1 / 20000 : ℝ) + 1 / (2 * 20000 ^ 2) < 1 / 16000 := by
  norm_num

theorem jensen_gain_after_truncation :
    (1 / 16000 : ℝ) <
      jensenEventProbability ^ 2 * (angularGini - angularMean / 3) -
        (1 / 20000 + 1 / (2 * 20000 ^ 2)) := by
  linarith [jensen_scalar_gain_gt, truncation_twenty_thousand_cost]

theorem explicit_rank_three_score_gap :
    (1 + 1 / 6000 : ℝ) <
      2 * (1 / Real.sqrt 2 + 1 / 16000) ^ 2 := by
  have hs : 0 < Real.sqrt (2 : ℝ) := by positivity
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hrec : (1 : ℝ) / Real.sqrt 2 = Real.sqrt 2 / 2 := by
    apply (div_eq_iff (ne_of_gt hs)).2
    nlinarith
  rw [hrec]
  nlinarith [sqrt_two_gt_seven_fifths]

theorem explicit_rank_three_normalized_derivative_gap :
    (1 - 2 * (1 / Real.sqrt 2 + 1 / 16000) ^ 2) / 4 <
      (-1 / 24000 : ℝ) := by
  linarith [explicit_rank_three_score_gap]

end QPermanentResearch
