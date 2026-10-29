module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Algebra.BigOperators.Fin

public section
noncomputable section
open scoped BigOperators
namespace MathAndTheory.BestOfN
/-- Reference mass strictly below the response i. -/
@[expose] def before {k : ℕ} (p : Fin k → ℝ) (i : Fin k) : ℝ :=
  ∑ j : Fin k, if j < i then p j else 0

/-- Reference mass at or below the response i. -/
@[expose] def through {k : ℕ} (p : Fin k → ℝ) (i : Fin k) : ℝ :=
  ∑ j : Fin k, if j ≤ i then p j else 0

/-- Exact selected probabilities for independent best-of-n sampling. -/
@[expose] def bestOfN {k : ℕ} (n : ℕ) (p : Fin k → ℝ) (i : Fin k) : ℝ :=
  through p i ^ n - before p i ^ n

/-- Direct enumeration of the independent two-draw experiment. -/
@[expose] def twoDrawMass {k : ℕ} (p : Fin k → ℝ) (i : Fin k) : ℝ :=
  ∑ a : Fin k, ∑ b : Fin k,
    if max a.val b.val = i.val then p a * p b else 0

/-- The half-credit win probability of q against an independent p. -/
@[expose] def winRate {k : ℕ} (q p : Fin k → ℝ) : ℝ :=
  ∑ i : Fin k, q i * (before p i + p i / 2)

/-- Kullback--Leibler divergence, selected law first. -/
@[expose] def kl {k : ℕ} (q p : Fin k → ℝ) : ℝ :=
  ∑ i : Fin k, q i * Real.log (q i / p i)

/-- The proposed continuous-reference tradeoff curve. -/
@[expose] def ell (w : ℝ) : ℝ := Real.log (w / (1 - w)) + 1 / w - 2

/-- The exact universal statement in its KL-versus-win-rate formulation. -/
@[expose] def UniversalCurve : Prop :=
  ∀ (k n : ℕ) (p : Fin k → ℝ),
    1 ≤ n → (∀ i, 0 < p i) → (∑ i : Fin k, p i) = 1 →
    ((1 / 2 : ℝ) ≤ winRate (bestOfN n p) p ∧ winRate (bestOfN n p) p < 1) →
    ell (winRate (bestOfN n p) p) ≤ kl (bestOfN n p) p

end MathAndTheory.BestOfN

namespace BestOfNChallenge
open MathAndTheory.BestOfN
theorem result : ¬ UniversalCurve := by
  sorry
theorem every_budget_small_atoms (n : ℕ) (hn : 2 ≤ n) (δ : ℝ) (hδ : 0 < δ) :
    ∃ (k : ℕ) (p : Fin k → ℝ),
      (∀ i, 0 < p i ∧ p i ≤ δ) ∧ (∑ i : Fin k, p i) = 1 ∧
      winRate (bestOfN n p) p ∈ Set.Ico (1 / 2 : ℝ) 1 ∧
      kl (bestOfN n p) p < ell (winRate (bestOfN n p) p) := by
  sorry
end BestOfNChallenge
