module
public import MathAndTheory.TheoreticalCS.BestOfN.Extension
public section
open scoped BigOperators
namespace BestOfNChallenge
open MathAndTheory.BestOfN
theorem result : ¬ UniversalCurve := by
  exact universal_curve_false
theorem every_budget_small_atoms (n : ℕ) (hn : 2 ≤ n) (δ : ℝ) (hδ : 0 < δ) :
    ∃ (k : ℕ) (p : Fin k → ℝ),
      (∀ i, 0 < p i ∧ p i ≤ δ) ∧ (∑ i : Fin k, p i) = 1 ∧
      winRate (bestOfN n p) p ∈ Set.Ico (1 / 2 : ℝ) 1 ∧
      kl (bestOfN n p) p < ell (winRate (bestOfN n p) p) := by
  exact MathAndTheory.BestOfNExtension.every_budget_small_atoms n hn δ hδ
end BestOfNChallenge
#print axioms BestOfNChallenge.result

#print axioms BestOfNChallenge.every_budget_small_atoms
