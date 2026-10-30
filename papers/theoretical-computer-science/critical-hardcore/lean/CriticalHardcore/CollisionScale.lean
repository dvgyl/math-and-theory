import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
Choose a fixed frontier length at the square-root scale. All constants are
explicit, and the final bound retains a natural ceiling logarithm, avoiding
unstated asymptotic constants in the graph theorem.
-/

namespace CriticalHardcore

def frontierLength (d n : ℕ) : ℕ := Nat.clog d (Nat.sqrt n + 1)

def collisionScale (d n : ℕ) : ℕ :=
  12 * d * (Nat.sqrt n + 1) * frontierLength d n

theorem frontierLength_pos {d n : ℕ} (hd : 2 ≤ d) (hn : 1 ≤ n) :
    1 ≤ frontierLength d n := by
  have hs : 1 ≤ Nat.sqrt n := Nat.le_sqrt.mpr (by simpa using hn)
  exact Nat.clog_pos (by omega) (by omega)

theorem frontier_power_lower {d n : ℕ} (hd : 2 ≤ d) :
    Nat.sqrt n + 1 ≤ d ^ frontierLength d n :=
  Nat.le_pow_clog (by omega) _

theorem frontier_power_upper {d n : ℕ} (hd : 2 ≤ d) (hn : 1 ≤ n) :
    d ^ frontierLength d n ≤ d * (Nat.sqrt n + 1) := by
  have hL := frontierLength_pos hd hn
  have hs : 1 ≤ Nat.sqrt n := Nat.le_sqrt.mpr (by simpa using hn)
  have hp := Nat.pow_pred_clog_lt_self (b := d) (x := Nat.sqrt n + 1)
    (by omega) (by omega)
  have hpow : d ^ frontierLength d n = d * d ^ (frontierLength d n - 1) := by
    conv_lhs => rw [← Nat.sub_add_cancel hL]
    rw [pow_succ']
  rw [hpow]
  exact Nat.mul_le_mul_left d (le_of_lt hp)

theorem good_budget_at_scale {d n : ℕ} (hd : 2 ≤ d) (hn : 1 ≤ n) :
    2 * n / d ^ (frontierLength d n - 1) ≤ 2 * d * (Nat.sqrt n + 1) := by
  have hL := frontierLength_pos hd hn
  have hp := frontier_power_lower (n := n) hd
  have hroot : n ≤ (Nat.sqrt n + 1) * (Nat.sqrt n + 1) :=
    le_of_lt (Nat.lt_succ_sqrt n)
  have hpow : d ^ frontierLength d n = d * d ^ (frontierLength d n - 1) := by
    conv_lhs => rw [← Nat.sub_add_cancel hL]
    rw [pow_succ']
  apply Nat.div_le_of_le_mul'
  calc
    2 * n ≤ 2 * ((Nat.sqrt n + 1) * (Nat.sqrt n + 1)) := Nat.mul_le_mul_left 2 hroot
    _ ≤ 2 * ((Nat.sqrt n + 1) * d ^ frontierLength d n) :=
      Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left (Nat.sqrt n + 1) hp)
    _ = d ^ (frontierLength d n - 1) * (2 * d * (Nat.sqrt n + 1)) := by
      rw [hpow]
      ring

/-- Explicit square-root times ceiling-logarithm control of the trial bound. -/
theorem collision_budget_le_scale {d n : ℕ} (hd : 2 ≤ d) (hn : 1 ≤ n) :
    (2 * frontierLength d n - 1) *
      (2 * n / d ^ (frontierLength d n - 1) + 4 * d ^ frontierLength d n) ≤
      collisionScale d n := by
  have hK := good_budget_at_scale hd hn
  have hp := frontier_power_upper hd hn
  have hsum : 2 * n / d ^ (frontierLength d n - 1) + 4 * d ^ frontierLength d n ≤
      6 * d * (Nat.sqrt n + 1) := by nlinarith
  calc
    _ ≤ (2 * frontierLength d n) * (6 * d * (Nat.sqrt n + 1)) :=
      Nat.mul_le_mul (Nat.sub_le _ _) hsum
    _ = collisionScale d n := by unfold collisionScale; ring

theorem frontierLength_le_binary {d n : ℕ} (hd : 2 ≤ d) :
    frontierLength d n ≤ Nat.clog 2 (Nat.sqrt n + 1) :=
  Nat.clog_anti_left (by decide) hd

end CriticalHardcore
