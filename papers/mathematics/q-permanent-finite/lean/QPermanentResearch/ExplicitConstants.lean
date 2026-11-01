import QPermanentResearch.JensenGap
import Mathlib.Data.Complex.ExponentialBounds

/-!
Exact scalar margins for the finite quantitative rank-three construction.
These arithmetic theorems do not assert the analytic concentration estimates
or the existence of a negative matrix certificate.
-/

namespace QPermanentResearch

theorem explicit_dilution_lower_bound {C : ℝ}
    (hC : 1 / Real.sqrt 2 + 1 / 16000 < C) (hC_one : C < 1) :
    1 / Real.sqrt 2 + 1 / 16000 - 3 / 1000000 <
      (999999 / 1000000 : ℝ) * C - 2 / 1000000 := by
  nlinarith

theorem explicit_coherent_floor_gap_strong :
    (1 + 1 / 6050 : ℝ) <
      2 * (1 / Real.sqrt 2 + 1 / 16000 - 3 / 1000000)^2 := by
  have hs : 0 < Real.sqrt (2 : ℝ) := by positivity
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hrec : (1 : ℝ) / Real.sqrt 2 = Real.sqrt 2 / 2 := by
    apply (div_eq_iff (ne_of_gt hs)).2
    nlinarith
  rw [hrec]
  nlinarith [sqrt_two_gt_seven_fifths]

theorem explicit_coherent_floor_gap :
    (1 + 4 / 25000 : ℝ) <
      2 * (1 / Real.sqrt 2 + 1 / 16000 - 3 / 1000000)^2 := by
  have h := explicit_coherent_floor_gap_strong
  linarith

/-- Two multiplicative mass losses of at most 10^-8 preserve the printed gap. -/
theorem explicit_gap_after_two_losses :
    (1 + 4 / 25000 : ℝ) <
      (1 - 1 / 100000000)^2 *
        (2 * (1 / Real.sqrt 2 + 1 / 16000 - 3 / 1000000)^2) := by
  have hpos : (0 : ℝ) < (1 - 1 / 100000000)^2 := by norm_num
  have hscaled := mul_lt_mul_of_pos_left explicit_coherent_floor_gap_strong hpos
  have hmargin : (1 + 4 / 25000 : ℝ) <
      (1 - 1 / 100000000)^2 * (1 + 1 / 6050) := by norm_num
  exact lt_trans hmargin hscaled

theorem explicit_gap_with_bounded_losses {u v : ℝ}
    (hu : 1 - 1 / 100000000 ≤ u) (hv : 1 - 1 / 100000000 ≤ v) :
    (1 + 4 / 25000 : ℝ) <
      u * v * (2 * (1 / Real.sqrt 2 + 1 / 16000 - 3 / 1000000)^2) := by
  have hbase : (0 : ℝ) ≤ 1 - 1 / 100000000 := by norm_num
  have huv : (1 - 1 / 100000000 : ℝ)^2 ≤ u * v := by
    rw [pow_two]
    exact mul_le_mul hu hv hbase (le_trans hbase hu)
  have hsquare : (0 : ℝ) ≤
      2 * (1 / Real.sqrt 2 + 1 / 16000 - 3 / 1000000)^2 := by positivity
  exact lt_of_lt_of_le explicit_gap_after_two_losses
    (mul_le_mul_of_nonneg_right huv hsquare)

theorem explicit_gap_after_three_losses :
    (1 + 4 / 25000 : ℝ) <
      (1 - 1 / 100000000)^3 *
        (2 * (1 / Real.sqrt 2 + 1 / 16000 - 3 / 1000000)^2) := by
  have hpos : (0 : ℝ) < (1 - 1 / 100000000)^3 := by norm_num
  have hscaled := mul_lt_mul_of_pos_left explicit_coherent_floor_gap_strong hpos
  have hmargin : (1 + 4 / 25000 : ℝ) <
      (1 - 1 / 100000000)^3 * (1 + 1 / 6050) := by norm_num
  exact lt_trans hmargin hscaled

theorem explicit_gap_with_three_bounded_losses {u v w : ℝ}
    (hu : 1 - 1 / 100000000 ≤ u) (hv : 1 - 1 / 100000000 ≤ v)
    (hw : 1 - 1 / 100000000 ≤ w) :
    (1 + 4 / 25000 : ℝ) <
      u * v * w * (2 * (1 / Real.sqrt 2 + 1 / 16000 - 3 / 1000000)^2) := by
  have hbase : (0 : ℝ) ≤ 1 - 1 / 100000000 := by norm_num
  have huv : (1 - 1 / 100000000 : ℝ)^2 ≤ u * v := by
    rw [pow_two]
    exact mul_le_mul hu hv hbase (le_trans hbase hu)
  have hprod : (1 - 1 / 100000000 : ℝ)^3 ≤ u * v * w := by
    calc
      _ = (1 - 1 / 100000000)^2 * (1 - 1 / 100000000) := by ring
      _ ≤ _ := mul_le_mul huv hw hbase
        (mul_nonneg (le_trans hbase hu) (le_trans hbase hv))
  have hsquare : (0 : ℝ) ≤
      2 * (1 / Real.sqrt 2 + 1 / 16000 - 3 / 1000000)^2 := by positivity
  exact lt_of_lt_of_le explicit_gap_after_three_losses
    (mul_le_mul_of_nonneg_right hprod hsquare)

theorem explicit_normalized_endpoint_gap :
    (1 - (1 - 1 / 100000000)^3 *
      (2 * (1 / Real.sqrt 2 + 1 / 16000 - 3 / 1000000)^2)) / 4 <
        (-1 / 25000 : ℝ) := by
  linarith [explicit_gap_after_three_losses]

theorem explicit_trigonometric_integer_bound : (3 : ℕ)^512 < 10^245 := by
  norm_num

theorem explicit_exp_one_bounds : (2 : ℝ) < Real.exp 1 ∧ Real.exp 1 < 3 := by
  constructor
  · linarith [Real.exp_one_gt_d9]
  · linarith [Real.exp_one_lt_d9]

theorem explicit_tilt_variance_gap :
    (1 / 2000000 : ℝ) < (1 - (999999 / 1000000)^2) / 2 := by
  norm_num

theorem explicit_cubic_neighborhood_error :
    (5 : ℝ) * 30000^3 * (1 / 10^22) < (1 / 1000000) / 4 := by
  norm_num

theorem explicit_log_error : (4096 : ℝ) * (1 / 10^60) < 1 / 10^52 := by
  norm_num

theorem explicit_fourth_moment_bound : (480 : ℕ) * (4 * 30000)^4 < 10^23 := by
  norm_num

theorem explicit_simultaneous_selection_error :
    (9 : ℝ) * 800000002 / (10^132 * (1 / 10^60)^2) < 1 / 2 := by
  norm_num

theorem explicit_denominator_mass_bound : (3 : ℝ) * 10^259 / 10^325 < 1 / 10^52 := by
  norm_num

theorem explicit_exterior_mass_error : (2 : ℝ) * 10^283 / 10^650 < 1 / 10^8 := by
  norm_num

theorem explicit_degree_error : (2 : ℝ) / 10^650 < 1 / 10^8 := by
  norm_num

theorem explicit_concentration_exponent : (30 : ℝ) ≤ (1 / 10^60) * 10^650 := by
  norm_num

theorem explicit_angular_tail : (8 : ℝ) / 2^256 < 1 / 10^74 := by
  norm_num

theorem explicit_K_squared : (30000 : ℕ)^2 < 2^30 := by
  norm_num

#print axioms explicit_dilution_lower_bound
#print axioms explicit_gap_after_two_losses
#print axioms explicit_gap_after_three_losses
#print axioms explicit_trigonometric_integer_bound
#print axioms explicit_exp_one_bounds
#print axioms explicit_tilt_variance_gap
#print axioms explicit_cubic_neighborhood_error
#print axioms explicit_log_error
#print axioms explicit_fourth_moment_bound
#print axioms explicit_simultaneous_selection_error
#print axioms explicit_denominator_mass_bound
#print axioms explicit_exterior_mass_error
#print axioms explicit_degree_error
#print axioms explicit_concentration_exponent
#print axioms explicit_angular_tail
#print axioms explicit_K_squared

end QPermanentResearch
