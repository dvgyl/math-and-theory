module

public import MathAndTheory.Mathematics.Motzkin.Definitions
public import MathAndTheory.Mathematics.Motzkin.Finite

@[expose] public section

/-!
# Solution of the source-defined Motzkin root problem

The proof identifies the finite sum with the recursive sequence.
It also proves existence and uniqueness for the source recurrence.
The final theorem therefore concerns the source definitions.
-/

namespace MathAndTheory.Motzkin.Source

open scoped BigOperators
open MathAndTheory.Motzkin.Challenge

theorem alternatingSum_zero (a : ℕ → ℚ) : alternatingSum a 0 = a 0 := by
  simp [alternatingSum]

theorem alternatingSum_succ (a : ℕ → ℚ) (n : ℕ) :
    alternatingSum a (n + 1) = a (n + 1) - alternatingSum a n := by
  unfold alternatingSum
  rw [Finset.sum_range_succ]
  have hneg :
      (∑ j ∈ Finset.range (n + 1), (-1 : ℚ) ^ (n + 1 - j) * a j) =
        -(∑ j ∈ Finset.range (n + 1), (-1 : ℚ) ^ (n - j) * a j) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    have hjn : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    rw [show n + 1 - j = (n - j) + 1 by omega, pow_succ]
    ring
  rw [hneg]
  simp only [Nat.sub_self, pow_zero, one_mul]
  ring

theorem alternatingSum_eq_alternating (n : ℕ) :
    alternatingSum motzkin n = alternating n := by
  induction n with
  | zero => simp [alternatingSum_zero]
  | succ n ih =>
      rw [alternatingSum_succ, ih]
      rfl

theorem motzkin_isMotzkin : IsMotzkin motzkin := by
  refine ⟨motzkin_zero, motzkin_one, ?_⟩
  intro n hn
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have hd : (j : ℚ) + 4 ≠ 0 := by positivity
  rw [show j + 1 + 1 = j + 2 by omega, motzkin_rec]
  simp only [Nat.cast_succ, Nat.succ_sub_one]
  field_simp [hd]
  ring

/-- The source recurrence has only one sequence with the stated initial values. -/
theorem eq_motzkin_of_isMotzkin {a : ℕ → ℚ} (ha : IsMotzkin a) :
    a = motzkin := by
  rcases ha with ⟨hzero, hone, hrec⟩
  funext n
  induction n using Nat.twoStepInduction with
  | zero => simpa using hzero
  | one => simpa using hone
  | more n ih₀ ih₁ =>
      have h := hrec (n + 1) (by omega)
      have hd : (n : ℚ) + 4 ≠ 0 := by positivity
      rw [motzkin_rec]
      apply (eq_div_iff hd).mpr
      simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel] at h
      rw [ih₀, ih₁] at h
      nlinarith

theorem alternatingSum_eq_of_isMotzkin {a : ℕ → ℚ} (ha : IsMotzkin a) (n : ℕ) :
    alternatingSum a n = alternating n := by
  rw [eq_motzkin_of_isMotzkin ha]
  exact alternatingSum_eq_alternating n

theorem nthRoot_eq_root {a : ℕ → ℚ} (ha : IsMotzkin a) (n : ℕ) :
    nthRoot a n = root n := by
  simp only [nthRoot, alternatingSum_eq_of_isMotzkin ha, root, T]

/-- Strict log-concavity for the finite sums in the source definition. -/
theorem finite_sum_roots_strict_log_concave {a : ℕ → ℚ}
    (ha : IsMotzkin a) (n : ℕ) (hn : 5 ≤ n) :
    nthRoot a n * nthRoot a (n + 2) < nthRoot a (n + 1) ^ (2 : ℕ) := by
  simpa only [nthRoot_eq_root ha] using roots_strict_log_concave n hn

/-- The source conjecture follows, with its stated starting index nine. -/
theorem zhao_conjecture_one {a : ℕ → ℚ} (ha : IsMotzkin a)
    (n : ℕ) (hn : 9 ≤ n) :
    nthRoot a n * nthRoot a (n + 2) ≤ nthRoot a (n + 1) ^ (2 : ℕ) :=
  (finite_sum_roots_strict_log_concave ha n (by omega)).le

/-- The center-five inequality is strictly reversed for the source finite sums. -/
theorem finite_sum_roots_sharp_failure {a : ℕ → ℚ} (ha : IsMotzkin a) :
    nthRoot a 5 ^ (2 : ℕ) < nthRoot a 4 * nthRoot a 6 := by
  simpa only [nthRoot_eq_root ha] using roots_sharp_failure

/-- Every earlier tail contains the failed center-five inequality. -/
theorem finite_sum_tail_start_optimal {a : ℕ → ℚ} (ha : IsMotzkin a)
    (start : ℕ) (hs : start ≤ 4) :
    ¬ (∀ n : ℕ, start ≤ n →
      nthRoot a n * nthRoot a (n + 2) ≤ nthRoot a (n + 1) ^ (2 : ℕ)) := by
  intro h
  have h4 := h 4 hs
  have hf := finite_sum_roots_sharp_failure ha
  norm_num only at h4
  exact (not_le_of_gt hf) h4

/-- The complete source-defined challenge. -/
theorem solution : MathAndTheory.Motzkin.Challenge.Problem := by
  refine ⟨⟨motzkin, motzkin_isMotzkin⟩, ?_⟩
  intro a ha
  exact ⟨finite_sum_roots_strict_log_concave ha,
    finite_sum_roots_sharp_failure ha, finite_sum_tail_start_optimal ha⟩

end MathAndTheory.Motzkin.Source
