import Mathlib.Tactic

namespace Kunisky
namespace Absorption

variable {σ : Type*} [DecidableEq σ]

/-- Probability that the absorbing target has not yet been reached after `k`
fair binary transitions.  The target has survival probability zero. -/
noncomputable def failure (target : σ) (left right : σ → σ) : ℕ → σ → ℝ
  | 0, s => if s = target then 0 else 1
  | k + 1, s => if s = target then 0 else
      (failure target left right k (left s) + failure target left right k (right s)) / 2

@[simp] theorem failure_target (target : σ) (left right : σ → σ) (k : ℕ) :
    failure target left right k target = 0 := by
  cases k <;> simp [failure]

theorem failure_nonneg (target : σ) (left right : σ → σ) (k : ℕ) (s : σ) :
    0 ≤ failure target left right k s := by
  induction k generalizing s with
  | zero => simp only [failure]; split <;> norm_num
  | succ k ih =>
    simp only [failure]
    split
    · norm_num
    · exact div_nonneg (add_nonneg (ih _) (ih _)) (by norm_num)

theorem failure_le_one (target : σ) (left right : σ → σ) (k : ℕ) (s : σ) :
    failure target left right k s ≤ 1 := by
  induction k generalizing s with
  | zero => simp only [failure]; split <;> norm_num
  | succ k ih =>
    simp only [failure]
    split
    · norm_num
    · have h₁ := ih (left s)
      have h₂ := ih (right s)
      linarith

/-- Every sequence of `k` first-child transitions reaches the target whenever
the initial rank is at most `k`.  It has probability at least `2⁻ᵏ`. -/
theorem failure_le_rank_bound (target : σ) (left right : σ → σ) (rank : σ → ℕ)
    (rank_zero : ∀ s, rank s = 0 → s = target)
    (rank_left : ∀ s, s ≠ target → rank (left s) < rank s)
    (k : ℕ) (s : σ) (hs : rank s ≤ k) :
    failure target left right k s ≤ 1 - (1 / 2 : ℝ) ^ k := by
  induction k generalizing s with
  | zero =>
    have heq : s = target := rank_zero s (by omega)
    subst s
    simp
  | succ k ih =>
    by_cases heq : s = target
    · subst s
      simp only [failure_target]
      have hp : (1 / 2 : ℝ) ^ (k + 1) ≤ 1 := by
        exact pow_le_one₀ (by norm_num) (by norm_num)
      linarith
    · have hr : rank (left s) ≤ k := by
        have := rank_left s heq
        omega
      have h₁ := ih (left s) hr
      have h₂ := failure_le_one target left right k (right s)
      simp only [failure, if_neg heq, pow_succ]
      linarith

/-- A uniform survival estimate remains valid after any further number of
transitions, with the same multiplicative factor. -/
theorem failure_shift_le (target : σ) (left right : σ → σ)
    (m : ℕ) (c : ℝ)
    (hbound : ∀ s, failure target left right m s ≤
      c * failure target left right 0 s) (k : ℕ) (s : σ) :
    failure target left right (m + k) s ≤ c * failure target left right k s := by
  induction k generalizing s with
  | zero => simpa using hbound s
  | succ k ih =>
    by_cases heq : s = target
    · subst s
      simp
    · have h₁ := ih (left s)
      have h₂ := ih (right s)
      simp only [Nat.add_succ, failure, if_neg heq]
      calc
        _ ≤ (c * failure target left right k (left s) +
          c * failure target left right k (right s)) / 2 :=
            div_le_div_of_nonneg_right (add_le_add h₁ h₂) (by norm_num)
        _ = _ := by ring

/-- A rank bounded by `n` gives a uniform contraction in each block of `n`
transitions.  This is a finite algebraic estimate, without a Markov-chain axiom. -/
theorem failure_blocks_le (target : σ) (left right : σ → σ) (rank : σ → ℕ)
    (rank_zero : ∀ s, rank s = 0 → s = target)
    (rank_left : ∀ s, s ≠ target → rank (left s) < rank s)
    (n : ℕ) (rank_bound : ∀ s, rank s ≤ n) (m : ℕ) (s : σ) :
    failure target left right (m * n) s ≤ (1 - (1 / 2 : ℝ) ^ n) ^ m := by
  have hp : (1 / 2 : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hc : 0 ≤ 1 - (1 / 2 : ℝ) ^ n := by linarith
  induction m generalizing s with
  | zero => simpa using failure_le_one target left right 0 s
  | succ m ih =>
    have hb : ∀ s, failure target left right (m * n) s ≤
        (1 - (1 / 2 : ℝ) ^ n) ^ m * failure target left right 0 s := by
      intro s
      by_cases heq : s = target
      · subst s; simp
      · simpa [failure, heq] using ih s
    have hshift := failure_shift_le target left right (m * n)
      ((1 - (1 / 2 : ℝ) ^ n) ^ m) hb n s
    have hr := failure_le_rank_bound target left right rank rank_zero rank_left n s
      (rank_bound s)
    calc
      failure target left right ((m + 1) * n) s =
          failure target left right (m * n + n) s := by rw [Nat.add_mul]; simp
      _ ≤ (1 - (1 / 2 : ℝ) ^ n) ^ m * failure target left right n s := hshift
      _ ≤ (1 - (1 / 2 : ℝ) ^ n) ^ m * (1 - (1 / 2 : ℝ) ^ n) :=
        mul_le_mul_of_nonneg_left hr (pow_nonneg hc _)
      _ = (1 - (1 / 2 : ℝ) ^ n) ^ (m + 1) := by rw [pow_succ]

/-- For every positive tolerance, a finite uniformly valid truncation depth
makes the surviving mass smaller than that tolerance at every state. -/
theorem exists_failure_lt (target : σ) (left right : σ → σ) (rank : σ → ℕ)
    (rank_zero : ∀ s, rank s = 0 → s = target)
    (rank_left : ∀ s, s ≠ target → rank (left s) < rank s)
    (n : ℕ) (rank_bound : ∀ s, rank s ≤ n) (ε : ℝ) (hε : 0 < ε) :
    ∃ m : ℕ, ∀ s, failure target left right (m * n) s < ε := by
  have hpos : 0 < (1 / 2 : ℝ) ^ n := pow_pos (by norm_num) _
  have hc : 1 - (1 / 2 : ℝ) ^ n < 1 := by linarith
  obtain ⟨m, hm⟩ : ∃ m : ℕ, (1 - (1 / 2 : ℝ) ^ n) ^ m < ε :=
    exists_pow_lt_of_lt_one hε hc
  refine ⟨m, fun s => lt_of_le_of_lt ?_ hm⟩
  exact failure_blocks_le target left right rank rank_zero rank_left n rank_bound m s

#print axioms failure_blocks_le
#print axioms exists_failure_lt

end Absorption
end Kunisky
