import DominationULC.Cycle
import DominationULC.CompositionCounts

namespace DominationULC

theorem boundedCycleCompositions_card_coefficient (n ell k : ℕ) :
    ((boundedCycleCompositions n ell k).card : ℝ) =
      (part (2 * ell + 1) ^ k) ((n + 1 : ℕ) : ℤ) := by
  classical
  have hc : (boundedCycleCompositions n ell k).card =
      Fintype.card {c : Composition (n + 1) //
        List.Forall₂ (· ≤ ·) c.blocks (List.replicate k (2 * ell + 1))} := by
    rw [Fintype.card_subtype]
    congr 1
    ext c
    simp only [boundedCycleCompositions, Finset.mem_filter, Finset.mem_univ, true_and]
    exact cycleGapGood_iff_forall₂ c
  rw [hc, boundedComposition_card]
  simp [gapSeq]

/-- The graph-theoretic domination coefficient and the bounded-gap convolution
coefficient satisfy the exact cyclic pointing identity. -/
theorem cycle_count_coefficient_succ (n ell k : ℕ) :
    (k : ℝ) * (dominationCount (cyclePower (n + 1) ell) k : ℝ) =
      (n + 1 : ℝ) * (part (2 * ell + 1) ^ k) ((n + 1 : ℕ) : ℤ) := by
  have h := cycle_count_compositions n ell k
  have hc : (k : ℝ) * (dominationCount (cyclePower (n + 1) ell) k : ℝ) =
      (n + 1 : ℝ) * ((boundedCycleCompositions n ell k).card : ℝ) := by
    exact_mod_cast h
  rwa [boundedCycleCompositions_card_coefficient] at hc

theorem cycle_count_coefficient {n ell k : ℕ} (hn : 0 < n) :
    (k : ℝ) * (dominationCount (cyclePower n ell) k : ℝ) =
      (n : ℝ) * (part (2 * ell + 1) ^ k) (n : ℤ) := by
  cases n with
  | zero => omega
  | succ n => simpa only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one]
      using cycle_count_coefficient_succ n ell k

end DominationULC
