module

public import MathAndTheory.Mathematics.Motzkin.Analysis
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-!
# Complete alternating-Motzkin root log-concavity theorem

The infinite range comes from the checked recurrence and real-analysis proof
in `MathAndTheory.Motzkin`. This file checks every remaining finite index with
proof-producing exact rational arithmetic and proves sharpness.
-/

namespace MathAndTheory.Motzkin

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000

/-- The exhaustive finite range: centers 6 through 30, inclusive. -/
theorem root_inequality_finite (n : ℕ) (h₅ : 5 ≤ n) (h₂₉ : n ≤ 29) :
    RootInequality n := by
  interval_cases n <;>
    norm_num [RootInequality, alternating, motzkin, motzkinPair]

/-- Strict root log-concavity at every center `n+1 >= 6`. -/
theorem root_inequality (n : ℕ) (hn : 5 ≤ n) : RootInequality n := by
  by_cases h : 30 ≤ n
  · exact root_inequality_infinite n h
  · exact root_inequality_finite n hn (by omega)

/-- Exact manuscript statement, using its original center-index convention. -/
theorem alternating_root_log_concavity (n : ℕ) (hn : 6 ≤ n) :
    alternating (n - 1) ^ (n * (n + 1)) * alternating (n + 1) ^ (n * (n - 1)) <
      alternating n ^ (2 * (n ^ 2 - 1)) := by
  cases n with
  | zero => omega
  | succ j =>
      have h := root_inequality j (by omega)
      have he : (j + 1) ^ 2 - 1 = j * (j + 2) := by
        apply Nat.sub_eq_of_eq_add
        ring
      change alternating j ^ ((j + 1) * (j + 2)) *
        alternating (j + 2) ^ ((j + 1) * j) <
        alternating (j + 1) ^ (2 * ((j + 1) ^ 2 - 1))
      rw [he]
      simpa [RootInequality, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h

/-- The inequality is strictly reversed at center five. -/
theorem sharp_failure :
    alternating 5 ^ 48 < alternating 4 ^ 30 * alternating 6 ^ 20 := by
  norm_num [alternating, motzkin, motzkinPair]

theorem exact_sharpness_difference :
    (37 : ℤ) ^ 10 - 2 ^ 24 * 7 ^ 9 = 4131563191399737 := by norm_num

/-- Weak log-concavity of the root tail beginning at `start`, in integer-power form. -/
def TailLogConcave (start : ℕ) : Prop := ∀ n, start ≤ n →
  alternating n ^ ((n + 1) * (n + 2)) * alternating (n + 2) ^ (n * (n + 1)) ≤
    alternating (n + 1) ^ (2 * n * (n + 2))

theorem tail_log_concave_from_five : TailLogConcave 5 := by
  intro n hn
  exact (root_inequality n hn).le

/-- Every earlier tail includes the strictly failed inequality centered at five. -/
theorem tail_start_optimal (start : ℕ) (hs : start ≤ 4) : ¬ TailLogConcave start := by
  intro h
  have h₄ := h 4 hs
  exact (not_le_of_gt sharp_failure) h₄

/-- The actual positive real nth root used in the manuscript. -/
noncomputable def root (n : ℕ) : ℝ := (T n) ^ (1 / (n : ℝ))

theorem root_pos (n : ℕ) (hn : 2 ≤ n) : 0 < root n :=
  Real.rpow_pos_of_pos (T_pos n hn) _

theorem log_root (n : ℕ) (hn : 2 ≤ n) :
    Real.log (root n) = Real.log (T n) / (n : ℝ) := by
  rw [root, Real.log_rpow (T_pos n hn)]
  ring

/-- Exact bridge between integer-power and actual real-root log-concavity. -/
theorem log_power_gap_eq_root_gap (n : ℕ) (hn : 2 ≤ n) :
    Real.log (T (n + 1) ^ (2 * n * (n + 2))) -
      Real.log (T n ^ ((n + 1) * (n + 2)) * T (n + 2) ^ (n * (n + 1))) =
    ((n : ℝ) * ((n : ℝ) + 1) * ((n : ℝ) + 2)) *
      (Real.log (root (n + 1) ^ (2 : ℕ)) - Real.log (root n * root (n + 2))) := by
  have hn₀ : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn₁ : (n : ℝ) + 1 ≠ 0 := by positivity
  have hn₂ : (n : ℝ) + 2 ≠ 0 := by positivity
  have ht₀ := T_pos n hn
  have ht₂ := T_pos (n + 2) (by omega)
  have hr₀ := root_pos n hn
  have hr₂ := root_pos (n + 2) (by omega)
  rw [Real.log_mul (pow_ne_zero _ ht₀.ne') (pow_ne_zero _ ht₂.ne'),
    Real.log_pow, Real.log_pow, Real.log_pow,
    Real.log_mul hr₀.ne' hr₂.ne', Real.log_pow,
    log_root n hn, log_root (n + 1) (by omega), log_root (n + 2) (by omega)]
  push_cast
  field_simp [hn₀.ne']

/-- Complete strict log-concavity theorem stated using actual real nth roots. -/
theorem roots_strict_log_concave (n : ℕ) (hn : 5 ≤ n) :
    root n * root (n + 2) < root (n + 1) ^ (2 : ℕ) := by
  have hn₂ : 2 ≤ n := by omega
  have hp : T n ^ ((n + 1) * (n + 2)) * T (n + 2) ^ (n * (n + 1)) <
      T (n + 1) ^ (2 * n * (n + 2)) := by
    have h := root_inequality n hn
    unfold RootInequality at h
    dsimp [T]
    exact_mod_cast h
  have hlog := Real.log_lt_log
    (mul_pos (pow_pos (T_pos n hn₂) _) (pow_pos (T_pos (n + 2) (by omega)) _)) hp
  have hgap : 0 < Real.log (T (n + 1) ^ (2 * n * (n + 2))) -
      Real.log (T n ^ ((n + 1) * (n + 2)) * T (n + 2) ^ (n * (n + 1))) := sub_pos.mpr hlog
  rw [log_power_gap_eq_root_gap n hn₂] at hgap
  have hd : 0 < (n : ℝ) * ((n : ℝ) + 1) * ((n : ℝ) + 2) := by
    have : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    positivity
  have hrlog : Real.log (root n * root (n + 2)) < Real.log (root (n + 1) ^ (2 : ℕ)) := by
    by_contra h
    have hnp : Real.log (root (n + 1) ^ (2 : ℕ)) - Real.log (root n * root (n + 2)) ≤ 0 := by
      linarith
    have hbad := mul_nonpos_of_nonneg_of_nonpos hd.le hnp
    linarith
  exact (Real.log_lt_log_iff
    (mul_pos (root_pos n hn₂) (root_pos (n + 2) (by omega)))
    (pow_pos (root_pos (n + 1) (by omega)) _)).mp hrlog

/-- The reverse inequality for the actual real roots proves the sharp start. -/
theorem roots_sharp_failure : root 5 ^ (2 : ℕ) < root 4 * root 6 := by
  have hp : T 5 ^ (48 : ℕ) < T 4 ^ (30 : ℕ) * T 6 ^ (20 : ℕ) := by
    dsimp [T]
    exact_mod_cast sharp_failure
  have hl := Real.log_lt_log (pow_pos (T_pos 5 (by omega)) _) hp
  have hgap := log_power_gap_eq_root_gap 4 (by omega)
  norm_num at hgap
  have hrootlog : Real.log (root 5 ^ (2 : ℕ)) < Real.log (root 4 * root 6) := by
    norm_num only [Real.log_pow, Nat.cast_ofNat] at hl ⊢
    linarith only [hl, hgap]
  exact (Real.log_lt_log_iff (pow_pos (root_pos 5 (by omega)) _)
    (mul_pos (root_pos 4 (by omega)) (root_pos 6 (by omega)))).mp hrootlog

end MathAndTheory.Motzkin
