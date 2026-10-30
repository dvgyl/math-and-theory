import CriticalHardcore.CollisionScale
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Real.Sqrt

/-! A real-variable interpretation of the explicit natural-number bound. -/

namespace CriticalHardcore

theorem nat_sqrt_cast_le_real_sqrt (n : ℕ) :
    (Nat.sqrt n : ℝ) ≤ Real.sqrt (n : ℝ) := by
  apply Real.le_sqrt_of_sq_le
  exact_mod_cast Nat.sqrt_le' n

theorem frontierLength_le_real_log {d n : ℕ} (hd : 2 ≤ d) :
    (frontierLength d n : ℝ) ≤ 1 + Real.logb (d : ℝ) (Real.sqrt (n : ℝ) + 1) := by
  have hd' : (1 : ℝ) < d := by exact_mod_cast (show 1 < d by omega)
  have hlog : 0 ≤ Real.logb (d : ℝ) ((Nat.sqrt n + 1 : ℕ) : ℝ) := by
    apply Real.logb_nonneg hd'
    exact_mod_cast (show 1 ≤ Nat.sqrt n + 1 by omega)
  have hceil := (Nat.ceil_lt_add_one hlog).le
  rw [Real.natCeil_logb_natCast] at hceil
  have hmono : Real.logb (d : ℝ) ((Nat.sqrt n + 1 : ℕ) : ℝ) ≤
      Real.logb (d : ℝ) (Real.sqrt (n : ℝ) + 1) := by
    apply Real.logb_le_logb_of_le hd'
    · positivity
    · simpa only [Nat.cast_add, Nat.cast_one] using
        add_le_add_right (nat_sqrt_cast_le_real_sqrt n) 1
  unfold frontierLength
  linarith

/-- The explicit walk bound has square-root times logarithmic growth. -/
theorem collisionScale_le_real {d n : ℕ} (hd : 2 ≤ d) :
    (collisionScale d n : ℝ) ≤
      12 * (d : ℝ) * (Real.sqrt (n : ℝ) + 1) *
        (1 + Real.logb (d : ℝ) (Real.sqrt (n : ℝ) + 1)) := by
  have hs := nat_sqrt_cast_le_real_sqrt n
  have hL := frontierLength_le_real_log (n := n) hd
  have hL0 : 0 ≤ (frontierLength d n : ℝ) := Nat.cast_nonneg _
  have hR0 : 0 ≤ Real.sqrt (n : ℝ) + 1 := by positivity
  have hlog0 : 0 ≤ 1 + Real.logb (d : ℝ) (Real.sqrt (n : ℝ) + 1) := hL0.trans hL
  unfold collisionScale
  push_cast
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_left (add_le_add_right hs 1) (by positivity)
  · exact hL
  · exact hL0
  · positivity

end CriticalHardcore
