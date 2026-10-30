import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace CPSharpness

/-- The positive root of the universal period-three obstruction polynomial. -/
noncomputable def threeCycleBoundary (θ : ℝ) : ℝ :=
  (1 + 3 * θ + Real.sqrt ((1 + 3 * θ) ^ 2 + 3 * (1 + θ) ^ 2)) / (1 + θ) ^ 2

private theorem quadratic_root_criterion {a b x : ℝ}
    (ha : 0 < a) (hx : 0 ≤ x) :
    0 ≤ a * x ^ 2 - 2 * b * x - 3 ↔
      (b + Real.sqrt (b ^ 2 + 3 * a)) / a ≤ x := by
  have hd : 0 ≤ b ^ 2 + 3 * a := by positivity
  have hs := Real.sqrt_nonneg (b ^ 2 + 3 * a)
  have hsq := Real.sq_sqrt hd
  rw [div_le_iff₀ ha]
  constructor
  · intro hp
    have hy : 0 ≤ a * x - b := by
      by_contra hh
      have hneg : a * x - b < 0 := lt_of_not_ge hh
      have hm := mul_nonpos_of_nonneg_of_nonpos hx (le_of_lt hneg)
      nlinarith
    have hmul := mul_nonneg (le_of_lt ha) hp
    have hsqdiff : (a * x - b) ^ 2 - (b ^ 2 + 3 * a) =
        a * (a * x ^ 2 - 2 * b * x - 3) := by ring
    nlinarith
  · intro hroot
    have hy : 0 ≤ a * x - b := by linarith
    have hprod := mul_nonneg (by linarith : 0 ≤ a * x - b - Real.sqrt (b ^ 2 + 3 * a))
      (by linarith : 0 ≤ a * x - b + Real.sqrt (b ^ 2 + 3 * a))
    have hsqdiff : (a * x - b) ^ 2 - (b ^ 2 + 3 * a) =
        a * (a * x ^ 2 - 2 * b * x - 3) := by ring
    have hmul : 0 ≤ a * (a * x ^ 2 - 2 * b * x - 3) := by nlinarith
    exact nonneg_of_mul_nonneg_right hmul ha

theorem polynomial_iff_boundary {κ θ : ℝ} (hκ : 0 ≤ κ) (hθ : 0 ≤ θ) :
    0 ≤ κ ^ 2 * (1 + θ) ^ 2 - 2 * κ * (1 + 3 * θ) - 3 ↔
      threeCycleBoundary θ ≤ κ := by
  have ha : 0 < (1 + θ) ^ 2 := by positivity
  simpa only [threeCycleBoundary, mul_comm ((1 + θ) ^ 2) (κ ^ 2),
    mul_comm (1 + 3 * θ) κ, mul_assoc, mul_left_comm] using
    (quadratic_root_criterion (b := 1 + 3 * θ) ha hκ)

private theorem quadratic_root_strict_criterion {a b x : ℝ}
    (ha : 0 < a) (hx : 0 ≤ x) :
    0 < a * x ^ 2 - 2 * b * x - 3 ↔
      (b + Real.sqrt (b ^ 2 + 3 * a)) / a < x := by
  have hd : 0 ≤ b ^ 2 + 3 * a := by positivity
  have hs := Real.sqrt_nonneg (b ^ 2 + 3 * a)
  have hsq := Real.sq_sqrt hd
  rw [div_lt_iff₀ ha]
  constructor
  · intro hp
    have hy : 0 ≤ a * x - b := by
      by_contra hh
      have hneg : a * x - b < 0 := lt_of_not_ge hh
      have hm := mul_nonpos_of_nonneg_of_nonpos hx (le_of_lt hneg)
      nlinarith
    have hmul := mul_pos ha hp
    have hsqdiff : (a * x - b) ^ 2 - (b ^ 2 + 3 * a) =
        a * (a * x ^ 2 - 2 * b * x - 3) := by ring
    nlinarith
  · intro hroot
    have hy : 0 < a * x - b := by linarith
    have hprod := mul_pos (by linarith : 0 < a * x - b - Real.sqrt (b ^ 2 + 3 * a))
      (by linarith : 0 < a * x - b + Real.sqrt (b ^ 2 + 3 * a))
    have hsqdiff : (a * x - b) ^ 2 - (b ^ 2 + 3 * a) =
        a * (a * x ^ 2 - 2 * b * x - 3) := by ring
    have hmul : 0 < a * (a * x ^ 2 - 2 * b * x - 3) := by nlinarith
    by_contra hh
    have hm := mul_nonpos_of_nonneg_of_nonpos ha.le (le_of_not_gt hh)
    linarith

theorem polynomial_pos_iff_boundary_lt {κ θ : ℝ} (hκ : 0 ≤ κ) (hθ : 0 ≤ θ) :
    0 < κ ^ 2 * (1 + θ) ^ 2 - 2 * κ * (1 + 3 * θ) - 3 ↔
      threeCycleBoundary θ < κ := by
  have ha : 0 < (1 + θ) ^ 2 := by positivity
  simpa only [threeCycleBoundary, mul_comm ((1 + θ) ^ 2) (κ ^ 2),
    mul_comm (1 + 3 * θ) κ, mul_assoc, mul_left_comm] using
    (quadratic_root_strict_criterion (b := 1 + 3 * θ) ha hκ)

theorem threeCycleBoundary_pos {θ : ℝ} (hθ : 0 ≤ θ) :
    0 < threeCycleBoundary θ := by
  unfold threeCycleBoundary
  positivity

theorem threeCycleBoundary_zero : threeCycleBoundary 0 = 3 := by
  norm_num [threeCycleBoundary]

/-- A concrete open interval of positive extrapolations where product three is
strictly inside the quadratic stability bound. -/
theorem product_three_below_quadratic {θ : ℝ} (hθ : 0 ≤ θ) (hsmall : θ < 1 / 6) :
    (3 : ℝ) < 4 / (1 + 2 * θ) := by
  rw [lt_div_iff₀ (by positivity : (0 : ℝ) < 1 + 2 * θ)]
  linarith

theorem boundary_at_most_three {θ : ℝ} (hθ : 0 ≤ θ) :
    threeCycleBoundary θ ≤ 3 := by
  apply (polynomial_iff_boundary (by norm_num : (0 : ℝ) ≤ 3) hθ).mp
  nlinarith [sq_nonneg θ]

theorem boundary_below_quadratic_iff {θ : ℝ} (hθ : 0 ≤ θ) :
    threeCycleBoundary θ < 4 / (1 + 2 * θ) ↔ 44 * θ ^ 2 + 20 * θ < 5 := by
  have hd : 0 < 1 + 2 * θ := by positivity
  have hq : 0 ≤ 4 / (1 + 2 * θ) := by positivity
  have hid : (1 + 2 * θ) ^ 2 *
      ((4 / (1 + 2 * θ)) ^ 2 * (1 + θ) ^ 2 -
      2 * (4 / (1 + 2 * θ)) * (1 + 3 * θ) - 3) = 5 - 20 * θ - 44 * θ ^ 2 := by
    field_simp
    ring
  rw [← polynomial_pos_iff_boundary_lt hq hθ]
  have hp : 0 < (1 + 2 * θ) ^ 2 := by positivity
  constructor
  · intro h
    have hm := mul_pos hp h
    rw [hid] at hm
    linarith
  · intro h
    have hm : 0 < (1 + 2 * θ) ^ 2 *
      ((4 / (1 + 2 * θ)) ^ 2 * (1 + θ) ^ 2 -
      2 * (4 / (1 + 2 * θ)) * (1 + 3 * θ) - 3) := by rw [hid]; linarith
    by_contra hh
    have hn := mul_nonpos_of_nonneg_of_nonpos hp.le (le_of_not_gt hh)
    linarith

theorem boundary_below_quadratic_exact_interval {θ : ℝ} (hθ : 0 ≤ θ) :
    threeCycleBoundary θ < 4 / (1 + 2 * θ) ↔ θ < (4 * Real.sqrt 5 - 5) / 22 := by
  rw [boundary_below_quadratic_iff hθ, lt_div_iff₀ (by norm_num : (0 : ℝ) < 22)]
  have hs := Real.sqrt_nonneg (5 : ℝ)
  have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  constructor <;> intro h <;> nlinarith

end CPSharpness
