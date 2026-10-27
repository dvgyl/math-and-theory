import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Tactic

/-!
# A centered two-point exponential bound

The proof uses the exponential chord on a symmetric interval and the
power-series inequality `Real.cosh_le_exp_half_sq` from mathlib.
-/

namespace PermEntropy

theorem two_point_exp_le (A B u v q t : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hq : 0 ≤ q)
    (hu : |u| ≤ q) (hv : |v| ≤ q) (hmean : A * u + B * v = 0) :
    A * Real.exp (t * u) + B * Real.exp (t * v) ≤
      (A + B) * Real.exp (q ^ 2 * t ^ 2 / 2) := by
  by_cases hq0 : q = 0
  · have hu0 : u = 0 := abs_eq_zero.mp (le_antisymm (hq0 ▸ hu) (abs_nonneg u))
    have hv0 : v = 0 := abs_eq_zero.mp (le_antisymm (hq0 ▸ hv) (abs_nonneg v))
    simp [hq0, hu0, hv0]
  have hqp : 0 < q := lt_of_le_of_ne hq (Ne.symm hq0)
  have hu' : |u / q| ≤ 1 := by
    rw [abs_div, abs_of_pos hqp, div_le_one hqp]
    exact hu
  have hv' : |v / q| ≤ 1 := by
    rw [abs_div, abs_of_pos hqp, div_le_one hqp]
    exact hv
  have heq (x : ℝ) : x / q * (t * q) = t * x := by field_simp; ring
  have heu := Real.exp_mul_le_cosh_add_mul_sinh hu' (t * q)
  have hev := Real.exp_mul_le_cosh_add_mul_sinh hv' (t * q)
  rw [heq] at heu hev
  have hm : A * (u / q) + B * (v / q) = 0 := by
    rw [← mul_div_assoc, ← mul_div_assoc, ← add_div, hmean, zero_div]
  calc
    A * Real.exp (t * u) + B * Real.exp (t * v) ≤
        A * (Real.cosh (t * q) + (u / q) * Real.sinh (t * q)) +
          B * (Real.cosh (t * q) + (v / q) * Real.sinh (t * q)) :=
      add_le_add (mul_le_mul_of_nonneg_left heu hA) (mul_le_mul_of_nonneg_left hev hB)
    _ = (A + B) * Real.cosh (t * q) := by
      have hm' := congrArg (fun z : ℝ => z * Real.sinh (t * q)) hm
      nlinarith only [hm']
    _ ≤ (A + B) * Real.exp ((t * q) ^ 2 / 2) :=
      mul_le_mul_of_nonneg_left (Real.cosh_le_exp_half_sq _) (add_nonneg hA hB)
    _ = (A + B) * Real.exp (q ^ 2 * t ^ 2 / 2) := by congr 2; ring

end PermEntropy
