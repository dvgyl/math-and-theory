import DominationULC.GraphCounts
import DominationULC.PathCounts
import DominationULC.PathCoefficients

namespace DominationULC

theorem path_domination_weighted_of_two_le (n ell j : ℕ) (hj : j + 2 < n) :
    (j + 3) * (n - (j + 2) + 1) *
        dominationCount (pathPower n ell) (j + 1) *
        dominationCount (pathPower n ell) (j + 3) ≤
      (j + 2) * (n - (j + 2)) * (dominationCount (pathPower n ell) (j + 2)) ^ 2 := by
  have hn : 0 < n := by omega
  have h := path_coeff_ulc (ell + 1) (2 * ell + 1) (by omega) ((n + 1 : ℕ) : ℤ) j
  rw [← path_dominationCount_eq_coefficient n ell j hn,
    ← path_dominationCount_eq_coefficient n ell (j + 2) hn,
    ← path_dominationCount_eq_coefficient n ell (j + 1) hn] at h
  have hcast :
      (((j + 3) * (n - (j + 2) + 1) *
          dominationCount (pathPower n ell) (j + 1) *
          dominationCount (pathPower n ell) (j + 3) : ℕ) : ℝ) ≤
        (((j + 2) * (n - (j + 2)) *
          (dominationCount (pathPower n ell) (j + 2)) ^ 2 : ℕ) : ℝ) := by
    push_cast
    rw [Nat.cast_sub (by omega : j + 2 ≤ n)]
    push_cast
    convert h using 1 <;> push_cast <;> ring
  exact_mod_cast hcast

/-- The weighted, denominator-free ultra-log-concavity inequality for every
power of every path, including all boundary and small-order cases. -/
theorem path_domination_weighted (n ell k : ℕ) (hk : 1 ≤ k) (hkn : k < n) :
    (k + 1) * (n - k + 1) * dominationCount (pathPower n ell) (k - 1) *
        dominationCount (pathPower n ell) (k + 1) ≤
      k * (n - k) * (dominationCount (pathPower n ell) k) ^ 2 := by
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
      path_domination_weighted_of_two_le n ell j (by omega)

/-- Galvin--Zhang Conjecture 1.8 for path powers. In fact the edgeless zeroth
power is covered as well. -/
theorem path_domination_ultraLogConcave (n ell : ℕ) :
    UltraLogConcave n (dominationCount (pathPower n ell)) := by
  intro k hk hkn
  exact normalized_logConcave_of_weighted _ hk hkn
    (path_domination_weighted n ell k hk hkn)

end DominationULC
