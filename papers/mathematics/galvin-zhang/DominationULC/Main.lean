import DominationULC.PathTheorem
import DominationULC.CycleTheorem

namespace DominationULC

/-- Galvin--Zhang Conjecture 1.8: the domination sequences of every power of
every finite path and every finite cycle are ultra-log-concave. -/
theorem galvin_zhang_conjecture (n ell : ℕ) :
    UltraLogConcave n (dominationCount (pathPower n ell)) ∧
      UltraLogConcave n (dominationCount (cyclePower n ell)) :=
  ⟨path_domination_ultraLogConcave n ell, cycle_domination_ultraLogConcave n ell⟩

/-- Explicit binomial-normalized inequalities, with the graph and count
definitions appearing directly in the theorem statement. -/
theorem galvin_zhang_normalized (n ell k : ℕ) (hk : 1 ≤ k) (hkn : k < n) :
    (((dominationCount (pathPower n ell) (k - 1) : ℝ) / (n.choose (k - 1) : ℝ)) *
        ((dominationCount (pathPower n ell) (k + 1) : ℝ) / (n.choose (k + 1) : ℝ)) ≤
      ((dominationCount (pathPower n ell) k : ℝ) / (n.choose k : ℝ)) ^ 2) ∧
    (((dominationCount (cyclePower n ell) (k - 1) : ℝ) / (n.choose (k - 1) : ℝ)) *
        ((dominationCount (cyclePower n ell) (k + 1) : ℝ) / (n.choose (k + 1) : ℝ)) ≤
      ((dominationCount (cyclePower n ell) k : ℝ) / (n.choose k : ℝ)) ^ 2) :=
  ⟨path_domination_ultraLogConcave n ell k hk hkn,
    cycle_domination_ultraLogConcave n ell k hk hkn⟩

end DominationULC

#print axioms DominationULC.galvin_zhang_conjecture
#print axioms DominationULC.galvin_zhang_normalized
#print axioms DominationULC.path_domination_weighted
#print axioms DominationULC.cycle_domination_weighted
