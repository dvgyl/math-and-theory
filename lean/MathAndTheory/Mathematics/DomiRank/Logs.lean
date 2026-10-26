module
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

@[expose] public section

namespace MathAndTheory.DomiRank

open Finset

/-- Exact finite bounds for a logarithm from the atanh series. -/
theorem log_interval_of_ratio {x t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (hx : x = (1 + t) / (1 - t)) (n : ℕ) :
    2 * (∑ i ∈ range n, t ^ (2 * i + 1) / (2 * i + 1)) ≤ Real.log x ∧
    Real.log x ≤ 2 * ((∑ i ∈ range n, t ^ (2 * i + 1) / (2 * i + 1)) +
      t ^ (2 * n + 1) / (1 - t ^ 2)) := by
  have hlo := Real.sum_range_le_log_div ht0 ht1 n
  have hhi := Real.log_div_le_sum_range_add ht0 ht1 n
  rw [← hx] at hlo hhi
  constructor <;> linarith

/-- A deliberately loose rational enclosure, established in the kernel. -/
theorem log_two_interval :
    (69314718055 : ℝ) / 100000000000 ≤ Real.log 2 ∧
    Real.log 2 ≤ (69314718057 : ℝ) / 100000000000 := by
  have h := log_interval_of_ratio (x := 2) (t := 1 / 3)
    (by norm_num) (by norm_num) (by norm_num) 12
  norm_num [Finset.sum_range_succ] at h
  constructor <;> linarith

end MathAndTheory.DomiRank
