import DominationULC.Path
import DominationULC.CompositionCounts
import Mathlib.Tactic.Ring

namespace DominationULC

theorem path_dominationCount_eq_gapSeq (n ell k : ℕ) (hn : 0 < n) :
    (dominationCount (pathPower n ell) (k + 1) : ℝ) =
      gapSeq (pathBounds ell k) ((n + 1 : ℕ) : ℤ) := by
  classical
  rw [path_dominationCount_eq_composition_card n ell k hn, Nat.card_eq_fintype_card]
  exact boundedComposition_card (n + 1) (pathBounds ell k)

theorem gapSeq_pathBounds (ell k : ℕ) :
    gapSeq (pathBounds ell k) = part (ell + 1) ^ 2 * part (2 * ell + 1) ^ k := by
  simp only [gapSeq, pathBounds, List.map_cons, List.map_append, List.map_replicate,
    List.map_singleton, List.prod_cons, List.prod_append, List.prod_replicate,
    List.prod_singleton, List.map_nil, List.prod_nil, mul_one]
  ring

/-- Exact coefficient formula for the graph-theoretic domination count of
every positive order path power and every positive rank. -/
theorem path_dominationCount_eq_coefficient (n ell k : ℕ) (hn : 0 < n) :
    (dominationCount (pathPower n ell) (k + 1) : ℝ) =
      (part (ell + 1) ^ 2 * part (2 * ell + 1) ^ k) ((n + 1 : ℕ) : ℤ) := by
  rw [path_dominationCount_eq_gapSeq n ell k hn, gapSeq_pathBounds]

end DominationULC
