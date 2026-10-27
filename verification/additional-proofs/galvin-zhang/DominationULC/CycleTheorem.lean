import DominationULC.GraphCounts
import DominationULC.CycleCounts
import DominationULC.CycleCoefficients

namespace DominationULC

theorem cycle_domination_weighted_of_two_le (n ell j : ℕ) (hj : j + 2 < n) :
    (j + 3) * (n - (j + 2) + 1) *
        dominationCount (cyclePower n ell) (j + 1) *
        dominationCount (cyclePower n ell) (j + 3) ≤
      (j + 2) * (n - (j + 2)) * (dominationCount (cyclePower n ell) (j + 2)) ^ 2 := by
  have hn : 0 < n := by omega
  let P : Seq := part (2 * ell + 1)
  let d : ℕ → ℝ := fun k => dominationCount (cyclePower n ell) k
  have hprev : (((j : ℝ) + 2) - 1) * d (j + 1) =
      (n : ℝ) * (P ^ (j + 1)) (n : ℤ) := by
    have h := cycle_count_coefficient (ell := ell) (k := j + 1) hn
    dsimp [d, P]
    convert h using 1
    push_cast
    ring
  have hcurr : ((j : ℝ) + 2) * d (j + 2) =
      (n : ℝ) * (P ^ (j + 2)) (n : ℤ) := by
    simpa only [d, P, Nat.cast_add, Nat.cast_ofNat]
      using cycle_count_coefficient (ell := ell) (k := j + 2) hn
  have hnext : (((j : ℝ) + 2) + 1) * d (j + 3) =
      (n : ℝ) * (P ^ (j + 3)) (n : ℤ) := by
    have h := cycle_count_coefficient (ell := ell) (k := j + 3) hn
    dsimp [d, P]
    convert h using 1
    push_cast
    ring
  have hcoef : ((j : ℝ) + 2) * ((n : ℝ) - ((j : ℝ) + 2) + 1) *
        (P ^ (j + 1)) (n : ℤ) * (P ^ (j + 3)) (n : ℤ) ≤
      (((j : ℝ) + 2) - 1) * ((n : ℝ) - ((j : ℝ) + 2)) *
        ((P ^ (j + 2)) (n : ℤ)) ^ 2 := by
    have h := cycle_coeff_ulc (2 * ell + 1) (n : ℤ) j
    dsimp [P]
    convert h using 1 <;> push_cast <;> ring
  have hR := cycle_pointing_ulc_transfer
    (by have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
        linarith : (1 : ℝ) < (j : ℝ) + 2) hprev hcurr hnext hcoef
  have hcast :
      (((j + 3) * (n - (j + 2) + 1) *
          dominationCount (cyclePower n ell) (j + 1) *
          dominationCount (cyclePower n ell) (j + 3) : ℕ) : ℝ) ≤
        (((j + 2) * (n - (j + 2)) *
          (dominationCount (cyclePower n ell) (j + 2)) ^ 2 : ℕ) : ℝ) := by
    push_cast
    rw [Nat.cast_sub (by omega : j + 2 ≤ n)]
    push_cast
    dsimp [d] at hR
    convert hR using 1
    ring
  exact_mod_cast hcast

/-- The weighted, denominator-free ultra-log-concavity inequality for every
power of every cycle, including all boundary and small-order cases. -/
theorem cycle_domination_weighted (n ell k : ℕ) (hk : 1 ≤ k) (hkn : k < n) :
    (k + 1) * (n - k + 1) * dominationCount (cyclePower n ell) (k - 1) *
        dominationCount (cyclePower n ell) (k + 1) ≤
      k * (n - k) * (dominationCount (cyclePower n ell) k) ^ 2 := by
  have hn : 0 < n := by omega
  letI : NeZero n := ⟨by omega⟩
  by_cases h₁ : k = 1
  · subst k
    simp [dominationCount_zero]
  · let j := k - 2
    have hj : j + 2 = k := by dsimp [j]; omega
    have hprev : j + 1 = k - 1 := by omega
    have hnext : j + 3 = k + 1 := by omega
    simpa only [hj, hprev, hnext] using
      cycle_domination_weighted_of_two_le n ell j (by omega)

/-- Galvin--Zhang Conjecture 1.8 for cycle powers. In fact the edgeless zeroth
power is covered as well. -/
theorem cycle_domination_ultraLogConcave (n ell : ℕ) :
    UltraLogConcave n (dominationCount (cyclePower n ell)) := by
  intro k hk hkn
  exact normalized_logConcave_of_weighted _ hk hkn
    (cycle_domination_weighted n ell k hk hkn)

end DominationULC
