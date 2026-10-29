module
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic


@[expose] public section

open Finset

namespace AsymmetricTutte

/-- Numerical statements used in the matroid induction.  The final theorem
discharges these statements from the explicit parameter-region inequalities. -/
structure ScalarInputs (x y : ℝ) : Prop where
  hx : 1 < x
  hy : 1 < y
  rank_one : ∀ k : ℕ, 2 ≤ k → (k : ℝ) ^ 2 ≤ x * ((∑ j ∈ range k, y ^ j) - 1)
  ordinary : ∀ A B U V s t : ℝ,
    0 ≤ A → 0 ≤ B → 0 ≤ U → 0 ≤ V → 0 ≤ s → 0 ≤ t →
    s ^ 2 ≤ A * U → t ^ 2 ≤ B * V → (s + t) ^ 2 ≤ (A + B) * (U + V)
  parallel : ∀ k : ℕ, 2 ≤ k → ∀ A B U V s t : ℝ,
    0 ≤ A → 0 ≤ B → 0 ≤ U → 0 ≤ V → 0 ≤ s → 0 ≤ t →
    (x - 1) * B ≤ A → (y - 1) * U ≤ V →
    s ^ 2 ≤ A * U → t ^ 2 ≤ B * V →
    (s + k * t) ^ 2 ≤ (A + B) * (U + (∑ j ∈ range k, y ^ j) * V)
  coloop : ∀ k : ℕ, 2 ≤ k → ∀ A B V s t : ℝ,
    0 ≤ A → 0 ≤ B → 0 ≤ V → 0 ≤ s → 0 ≤ t →
    (x - 1) * B ≤ A → t ^ 2 ≤ B * V → 2 * s ≤ t →
    (s + k * t) ^ 2 ≤ (A + B) * ((∑ j ∈ range k, y ^ j) * V)


end AsymmetricTutte
