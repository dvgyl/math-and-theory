import QPermanentResearch.ExplicitConstants
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
Exact scalar bounds for the stronger spherical Gini estimate and the
fixed-parameter mean-field construction. Probability identities, saddle
concentration and the asymptotic matrix theorem are not proved here.
-/

namespace QPermanentResearch

noncomputable def strongSphericalGiniGain : ℝ :=
  (Real.pi ^ 2 - 8) / (32 * Real.sqrt 2 * Real.pi)

theorem strongSphericalGiniGain_gt :
    (13 / 1000 : ℝ) < strongSphericalGiniGain := by
  have hs0 : 0 < Real.sqrt (2 : ℝ) := by positivity
  have hs2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hs : Real.sqrt (2 : ℝ) < 283 / 200 := by nlinarith
  have hp : (157 / 50 : ℝ) < Real.pi := by linarith [Real.pi_gt_d4]
  have hpu := pi_lt_twenty_two_sevenths
  have hprod : Real.sqrt (2 : ℝ) * Real.pi < (283 / 200) * (22 / 7) :=
    mul_lt_mul hs hpu.le (by positivity) (by norm_num)
  unfold strongSphericalGiniGain
  apply (lt_div_iff₀ (by positivity : (0 : ℝ) < 32 * Real.sqrt 2 * Real.pi)).2
  nlinarith

theorem meanField_radial_loss {k : ℝ} (hk : 25000 ≤ k) :
    Real.sqrt 2 / Real.sqrt k < (9 / 1000 : ℝ) := by
  have hk0 : 0 < k := by linarith
  have hs0 : 0 < Real.sqrt k := Real.sqrt_pos.2 hk0
  have hs2 := Real.sq_sqrt hk0.le
  have h20 := Real.sqrt_nonneg (2 : ℝ)
  have h22 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  apply (div_lt_iff₀ hs0).2
  nlinarith

theorem meanField_log_25001_lt : Real.log 25001 < (15 : ℝ) := by
  apply (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 25001)).2
  have hp : (2 : ℝ)^15 < (Real.exp 1)^15 :=
    pow_lt_pow_left₀ explicit_exp_one_bounds.1 (by norm_num) (by decide)
  have heq : Real.exp (15 : ℝ) = (Real.exp 1)^15 := by
    simpa using Real.exp_nat_mul (1 : ℝ) 15
  rw [heq]
  norm_num at hp ⊢
  linarith

theorem meanField_log_loss {k : ℝ} (hk : 25000 ≤ k) :
    Real.log (1 + k) / k < (1 / 1000 : ℝ) := by
  have hk0 : 0 < k := by linarith
  have hkp : 0 < 1 + k := by linarith
  have hdiv : 0 < (1 + k) / 25001 := by positivity
  have hlog := Real.log_le_sub_one_of_pos hdiv
  rw [Real.log_div (ne_of_gt hkp) (by norm_num : (25001 : ℝ) ≠ 0)] at hlog
  apply (div_lt_iff₀ hk0).2
  linarith [meanField_log_25001_lt]

theorem meanField_total_radial_loss {k : ℝ} (hk : 25000 ≤ k) :
    Real.sqrt 2 / Real.sqrt k + Real.log (1 + k) / k < (1 / 100 : ℝ) := by
  linarith [meanField_radial_loss hk, meanField_log_loss hk]

theorem meanField_contracted_gini_floor {C loss : ℝ}
    (hC : 1 / Real.sqrt 2 + strongSphericalGiniGain ≤ C)
    (hloss : loss < 1 / 100) :
    1 / Real.sqrt 2 + 1 / 500 < (999 / 1000 : ℝ) * (C - loss) := by
  have hgain := strongSphericalGiniGain_gt
  have hrec := inv_sqrt_two_lt
  linarith

theorem meanField_score_floor :
    (1 + 1 / 200 : ℝ) < 2 * (1 / Real.sqrt 2 + 1 / 500)^2 := by
  have hs : 0 < Real.sqrt (2 : ℝ) := by positivity
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hrec : (1 : ℝ) / Real.sqrt 2 = Real.sqrt 2 / 2 := by
    apply (div_eq_iff (ne_of_gt hs)).2
    nlinarith
  rw [hrec]
  nlinarith [sqrt_two_gt_seven_fifths]

theorem meanField_normalized_derivative_floor :
    (1 - 2 * (1 / Real.sqrt 2 + 1 / 500)^2) / 4 < (-1 / 800 : ℝ) := by
  linarith [meanField_score_floor]

theorem meanField_limit_condition : (1 : ℝ) + 60000 / 3 = 20001 := by norm_num

end QPermanentResearch
