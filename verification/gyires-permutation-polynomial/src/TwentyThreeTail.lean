module

public import WeightedNormalized
public import ThirtyNineTail
public import Mathlib.Tactic.IntervalCases

@[expose] public section

namespace MathAndTheory.Gyires.PermutationTransfer.Sharp.WeightedBound

theorem prefactor_succ_le (n : ℕ) (hn : 4 ≤ n) : prefactor (n+1) ≤ K*prefactor n := by
  have hp : 0 ≤ (2:ℝ)^n := by positivity
  have hexp : n+1-4 = (n-4)+1 := by omega
  unfold prefactor
  rw [hexp, pow_succ, pow_succ]
  dsimp [K]
  nlinarith

theorem rational_growth_lower (n : ℕ) (hn : 23 ≤ n) :
    K*(n:ℝ)^n < ((n:ℝ)+1)^n := by
  by_cases hn39 : 39 ≤ n
  · exact TwoBound.rational_growth_lower n hn39
  have hhi : n ≤ 38 := by omega
  interval_cases n <;> norm_num [K]

theorem rational_tail_integer (n : ℕ) (hn : 23 ≤ n) :
    prefactor n * (n.factorial:ℝ) < (n:ℝ)^n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num [prefactor, K, Nat.factorial]
  | succ n hn ih =>
      have hnp : (0:ℝ) < (n:ℝ)+1 := by positivity
      have hfac : (0:ℝ) ≤ n.factorial := by positivity
      have hstep : prefactor (n+1)*(n.factorial:ℝ) < ((n:ℝ)+1)^n := by
        calc
          prefactor (n+1)*(n.factorial:ℝ) ≤
              (K*prefactor n)*(n.factorial:ℝ) :=
            mul_le_mul_of_nonneg_right (prefactor_succ_le n (by omega)) hfac
          _ = K*(prefactor n*(n.factorial:ℝ)) := by ring
          _ < K*(n:ℝ)^n := mul_lt_mul_of_pos_left ih K_pos
          _ < ((n:ℝ)+1)^n := rational_growth_lower n hn
      have hfinal := mul_lt_mul_of_pos_left hstep hnp
      rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
      nlinarith

theorem rational_tail (n : ℕ) (hn : 23 ≤ n) :
    dimensionConstant n * prefactor n < 1 := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hp : (0:ℝ) < (n:ℝ)^n := pow_pos hn0 n
  have h := rational_tail_integer n hn
  unfold dimensionConstant
  apply (mul_lt_mul_iff_right₀ hp).mp
  field_simp
  simpa [mul_comm] using h

end MathAndTheory.Gyires.PermutationTransfer.Sharp.WeightedBound
